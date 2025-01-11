// SPDX-License-Identifier: APACHE-2.0

package dnscache

import (
	"context"
	"fmt"
	"net"
	"os"
	"strings"
	"sync"
	"syscall"
	"time"

	"github.com/florianl/go-nfqueue"
	"github.com/google/logger"
	"github.com/google/nftables"
	"github.com/google/nftables/binaryutil"
	"github.com/google/nftables/expr"
	"github.com/mdlayher/netlink"

	"golang.org/x/net/dns/dnsmessage"
	"golang.org/x/sys/unix"
	utilerrors "k8s.io/apimachinery/pkg/util/errors"
	coreinformers "k8s.io/client-go/informers/core/v1"
	v1 "k8s.io/client-go/listers/core/v1"
	"k8s.io/client-go/tools/cache"
	"k8s.io/klog/v2"
	"k8s.io/utils/clock"
	utilio "k8s.io/utils/io"
	"sigs.k8s.io/knftables"
)

// reference https://coredns.io/plugins/cache/
const (
	tableName = "kindnet-dnscache"
	queueID   = 103
	// same as LocalNodeDNS
	// https://github.com/kubernetes/dns/blob/c0fa2d1128d42c9b13e08a6a7e3ee8c635b9acd5/cmd/node-cache/Corefile#L3
	expireTimeout = 30 * time.Second
	// It was 512 byRFC1035 for UDP until EDNS, but large packets can be fragmented ...
	// it seems bind uses 1232 as maximum size
	// https://kb.isc.org/docs/behavior-dig-versions-edns-bufsize
	maxDNSSize = 1232
)

// NewDNSCacheAgent caches all DNS traffic from Pods with network based on the PodCIDR of the node they are running.
// Cache logic is very specific to Kubernetes,
func NewDNSCacheAgent(nodeName string, nodeInformer coreinformers.NodeInformer) (*DNSCacheAgent, error) {
	klog.V(2).Info("Initializing nftables")
	nft, err := knftables.New(knftables.InetFamily, "kindnet-dnscache")
	if err != nil {
		return nil, err
	}

	d := &DNSCacheAgent{
		nft:         nft,
		nodeName:    nodeName,
		nodeLister:  nodeInformer.Lister(),
		nodesSynced: nodeInformer.Informer().HasSynced,
		interval:    5 * time.Minute,
		cache:       newIPCache(),
	}

	return d, nil
}

// DNSCacheAgent caches all DNS traffic from Pods with network based on the PodCIDR of the node they are running.
// Cache logic is very specific to Kubernetes,
type DNSCacheAgent struct {
	nft         knftables.Interface
	nodeName    string
	nodeLister  v1.NodeLister
	nodesSynced cache.InformerSynced
	interval    time.Duration

	podCIDRv4  string
	podCIDRv6  string
	nameServer string
	searches   []string
	flushed    bool

	localAddr string // UDP server listener address
	resolver  *net.Resolver
	cache     *ipCache
}

type ipEntry struct {
	ts  time.Time
	ips []net.IP
}

type ipCache struct {
	mu             sync.RWMutex
	clock          clock.Clock
	cacheV4Address map[string]ipEntry
	cacheV6Address map[string]ipEntry
}

func (i *ipCache) add(network string, host string, ips []net.IP) {
	i.mu.Lock()
	defer i.mu.Unlock()
	now := i.clock.Now()
	entry := ipEntry{
		ts:  now,
		ips: ips,
	}
	if network == "ip6" {
		i.cacheV6Address[host] = entry
		dnsCacheSize.WithLabelValues("ip6").Set(float64(len(i.cacheV6Address)))
	}
	if network == "ip4" {
		i.cacheV4Address[host] = entry
		dnsCacheSize.WithLabelValues("ip4").Set(float64(len(i.cacheV4Address)))
	}
}

func (i *ipCache) get(network string, host string) ([]net.IP, bool) {
	i.mu.RLock()
	defer i.mu.RUnlock()
	var entry ipEntry
	var ok bool

	if network == "ip6" {
		entry, ok = i.cacheV6Address[host]
	}
	if network == "ip4" {
		entry, ok = i.cacheV4Address[host]
	}
	if !ok {
		return nil, false
	}
	// check if the entry is still valid
	if entry.ts.Add(expireTimeout).Before(i.clock.Now()) {
		i.delete(network, host)
		return nil, false
	}
	return entry.ips, true
}

func (i *ipCache) delete(network string, host string) {
	if network == "ip6" {
		delete(i.cacheV6Address, host)
		dnsCacheSize.WithLabelValues("ip6").Set(float64(len(i.cacheV6Address)))
	}
	if network == "ip4" {
		delete(i.cacheV4Address, host)
		dnsCacheSize.WithLabelValues("ip4").Set(float64(len(i.cacheV4Address)))
	}
}

func (i *ipCache) gc() {
	i.mu.Lock()
	defer i.mu.Unlock()
	now := i.clock.Now()
	for host, entry := range i.cacheV4Address {
		// check if the entry is still valid
		if entry.ts.Add(expireTimeout).Before(now) {
			i.delete("ip4", host)
		}
	}
	for host, entry := range i.cacheV6Address {
		// check if the entry is still valid
		if entry.ts.Add(expireTimeout).Before(now) {
			i.delete("ip6", host)
		}
	}
	dnsCacheSize.WithLabelValues("ip4").Set(float64(len(i.cacheV4Address)))
	dnsCacheSize.WithLabelValues("ip6").Set(float64(len(i.cacheV6Address)))
}

func newIPCache() *ipCache {
	return &ipCache{
		cacheV4Address: map[string]ipEntry{},
		cacheV6Address: map[string]ipEntry{},
		clock:          clock.RealClock{},
	}
}

// Run syncs dns cache intercept rules
func (d *DNSCacheAgent) Run(ctx context.Context) error {
	registerMetrics()

	if !cache.WaitForNamedCacheSync("kindnet-dnscache", ctx.Done(), d.nodesSynced) {
		return fmt.Errorf("error syncing cache")
	}
	// kindnet is using hostNetwork and dnsPolicy: ClusterFirstWithHostNet
	// so its resolv.conf will have the configuration from the network Pods
	klog.Info("Configuring upstream DNS resolver")
	hostDNS, hostSearch, hostOptions, err := parseResolvConf()
	if err != nil {
		err := fmt.Errorf("encountered error while parsing resolv conf file. Error: %w", err)
		klog.ErrorS(err, "Could not parse resolv conf file.")
		return err
	}
	d.nameServer = hostDNS[0]
	d.searches = hostSearch
	klog.V(2).Infof("Parsed resolv.conf: nameservers: %v search: %v options: %v", hostDNS, hostSearch, hostOptions)

	var flags uint32
	// https://netfilter.org/projects/libnetfilter_queue/doxygen/html/group__Queue.html
	// the kernel will not normalize offload packets,
	// i.e. your application will need to be able to handle packets larger than the mtu.
	// Normalization is expensive, so this flag should always be set.
	// This also solves a bug with SCTP
	// https://github.com/aojea/kube-netpol/issues/8
	// https://bugzilla.netfilter.org/show_bug.cgi?id=1742
	flags = nfqueue.NfQaCfgFlagGSO
	if c.config.FailOpen {
		flags += nfqueue.NfQaCfgFlagFailOpen
	}

	// Set configuration options for nfqueue
	config := nfqueue.Config{
		NfQueue:      uint16(c.config.QueueID),
		Flags:        flags,
		MaxPacketLen: 128, // only interested in the headers
		MaxQueueLen:  1024,
		Copymode:     nfqueue.NfQnlCopyPacket, // headers
		WriteTimeout: 100 * time.Millisecond,
	}

	nf, err := nfqueue.Open(&config)
	if err != nil {
		logger.Info("could not open nfqueue socket", "error", err)
		return err
	}
	defer nf.Close()

	c.nfq = nf

	// Parse the packet and check if it should be accepted
	// Packets should be evaludated independently in each direction
	fn := func(a nfqueue.Attribute) int {
		verdict := nfqueue.NfDrop
		if c.config.FailOpen {
			verdict = nfqueue.NfAccept
		}

		startTime := time.Now()
		logger.V(2).Info("Processing sync for packet", "id", *a.PacketID)

		packet, err := parsePacket(*a.Payload)
		if err != nil {
			logger.Error(err, "Can not process packet, applying default policy", "id", *a.PacketID, "failOpen", c.config.FailOpen)
			c.nfq.SetVerdict(*a.PacketID, verdict) //nolint:errcheck
			return 0
		}
		packet.id = *a.PacketID

		defer func() {
			processingTime := float64(time.Since(startTime).Microseconds())
			packetProcessingHist.WithLabelValues(string(packet.proto), string(packet.family)).Observe(processingTime)
			packetProcessingSum.Observe(processingTime)
			verdictStr := verdictString(verdict)
			packetCounterVec.WithLabelValues(string(packet.proto), string(packet.family), verdictStr).Inc()
			logger.V(2).Info("Finished syncing packet", "id", *a.PacketID, "duration", time.Since(startTime), "verdict", verdictStr)
		}()

		if c.evaluatePacket(ctx, packet) {
			verdict = nfqueue.NfAccept
		} else {
			verdict = nfqueue.NfDrop
		}
		c.nfq.SetVerdict(*a.PacketID, verdict) //nolint:errcheck
		return 0
	}

	// Register your function to listen on nflog group 100
	err = nf.RegisterWithErrorFunc(ctx, fn, func(err error) int {
		if opError, ok := err.(*netlink.OpError); ok {
			if opError.Timeout() || opError.Temporary() {
				return 0
			}
		}
		logger.Info("Could not receive message", "error", err)
		return 0
	})
	if err != nil {
		logger.Info("could not open nfqueue socket", "error", err)
		return err
	}

	errs := 0
	ticker := time.NewTicker(d.interval)
	defer ticker.Stop()
	for {
		if ctx.Err() != nil {
			return ctx.Err()
		}

		if err := d.SyncRules(ctx); err != nil {
			errs++
			if errs > 3 {
				return fmt.Errorf("can't synchronize rules after 3 attempts: %v", err)
			}
		} else {
			errs = 0
		}
		// garbage collect ip cache entries
		d.cache.gc()
		select {
		case <-ctx.Done():
			return ctx.Err()
		case <-ticker.C:
			continue
		}
	}
}

func (d *DNSCacheAgent) serveDNS(addr net.Addr, data []byte) {
	// it must answer with the origin the DNS server used to cache
	// and destination the same original address
	klog.V(2).Infof("dialing from %s:%d to %s", d.nameServer, 53, addr.String())
	bypassFreebindDialer := &net.Dialer{
		LocalAddr: &net.UDPAddr{IP: net.ParseIP(d.nameServer), Port: 53},
		Control: func(network, address string, c syscall.RawConn) error {
			return c.Control(func(fd uintptr) {
				// Mark connections so thet are not processed by the netfilter TPROXY rules
				if err := unix.SetsockoptInt(int(fd), syscall.SOL_SOCKET, syscall.SO_MARK, tproxyBypassMark); err != nil {
					klog.Infof("setting SO_MARK bypass: %v", err)
				}
				if err := unix.SetsockoptInt(int(fd), syscall.SOL_IP, syscall.IP_TRANSPARENT, 1); err != nil {
					klog.Infof("setting IP_TRANSPARENT: %v", err)
				}
				if err := unix.SetsockoptInt(int(fd), syscall.SOL_SOCKET, unix.SO_REUSEPORT, 1); err != nil {
					klog.Infof("setting SO_REUSEPORT: %v", err)
				}
			})
		},
	}
	conn, err := bypassFreebindDialer.Dial("udp", addr.String())
	if err != nil {
		klog.Infof("can not dial to %s : %v", addr.String(), err)
		return
	}
	_, err = conn.Write(d.dnsPacketRoundTrip(data))
	if err != nil {
		klog.Infof("error writing DNS answer: %v", err)
	}
}

// SyncRules syncs ip masquerade rules
func (d *DNSCacheAgent) SyncRules(ctx context.Context) error {
	klog.FromContext(ctx).Info("Syncing nftables rules")
	nft, err := nftables.New()
	if err != nil {
		return fmt.Errorf("can not start nftables:%v", err)
	}
	// add + delete + add for flushing all the table
	table := &nftables.Table{
		Name:   tableName,
		Family: nftables.TableFamilyINet,
	}

	nft.AddTable(table)
	nft.DelTable(table)
	nft.AddTable(table)

	chain := nft.AddChain(&nftables.Chain{
		Name:     "prerouting",
		Table:    table,
		Type:     nftables.ChainTypeFilter,
		Hooknum:  nftables.ChainHookPrerouting, // packets not generated on the hosts
		Priority: nftables.ChainPriorityRaw,    // just before conntrack
	})

	// TODO: restrict this more, maybe iiftype == veth, we want to handle the traffic
	// from the Pods to dns servers out of the own host, as it is unlikely that caching/proxying the local traffic will add any benefit.
	// udp dport 53 queue flag bypass
	nft.AddRule(&nftables.Rule{
		Table: table,
		Chain: chain,
		Exprs: []expr.Any{
			&expr.Meta{Key: expr.MetaKeyL4PROTO, SourceRegister: false, Register: 0x1},
			&expr.Cmp{Op: expr.CmpOpEq, Register: 0x1, Data: []byte{unix.IPPROTO_UDP}},
			&expr.Payload{DestRegister: 0x1, Base: expr.PayloadBaseTransportHeader, Offset: 2, Len: 2},
			&expr.Cmp{Op: expr.CmpOpEq, Register: 0x1, Data: binaryutil.BigEndian.PutUint16(53)},
			&expr.Queue{Num: queueID, Flag: expr.QueueFlagBypass},
		},
	})

	if err := nft.Flush(); err != nil {
		klog.Infof("error syncing nftables rules %v", err)
		return err
	}
	return nil
}

func (d *DNSCacheAgent) CleanRules() {
	nft, err := nftables.New()
	if err != nil {
		klog.Errorf("can not start nftables:%v", err)
		return
	} // Add+Delete is idempotent and won't return an error if the table doesn't already
	// exist.
	table := &nftables.Table{
		Name:   tableName,
		Family: nftables.TableFamilyINet,
	}

	nft.AddTable(table)
	nft.DelTable(table)

	if err := nft.Flush(); err != nil {
		klog.Infof("error deleting nftables rules %v", err)
	}
}

func (d *DNSCacheAgent) dnsPacketRoundTrip(b []byte) []byte {
	var p dnsmessage.Parser
	klog.V(7).Info("starting parsing packet")
	hdr, err := p.Start(b)
	if err != nil {
		return dnsErrorMessage(hdr.ID, dnsmessage.RCodeFormatError, dnsmessage.Question{})
	}
	if len(b) > maxDNSSize {
		return dnsErrorMessage(hdr.ID, dnsmessage.RCodeFormatError, dnsmessage.Question{})
	}

	questions, err := p.AllQuestions()
	if err != nil {
		return dnsErrorMessage(hdr.ID, dnsmessage.RCodeFormatError, dnsmessage.Question{})
	}
	if len(questions) == 0 {
		return dnsErrorMessage(hdr.ID, dnsmessage.RCodeFormatError, dnsmessage.Question{})
	}
	// it is supported but not wildly implemented, at least not in golang stdlib
	if len(questions) > 1 {
		answer, err := d.passThrough(b)
		if err != nil {
			return dnsErrorMessage(hdr.ID, dnsmessage.RCodeServerFailure, questions...)
		}
		if len(answer) > maxDNSSize {
			answer = dnsTruncatedMessage(hdr.ID, questions...)
		}
		return answer
	}
	question := questions[0]
	answer, delegate := d.processDNSRequest(hdr.ID, question)
	// pass it through
	if delegate {
		klog.V(7).Info("can not process request, delegating ...")
		answer, err = d.passThrough(b)
		if err != nil {
			return dnsErrorMessage(hdr.ID, dnsmessage.RCodeServerFailure, question)
		}
		// Return a truncated packet if the answer is too big
		if len(answer) > maxDNSSize {
			answer = dnsTruncatedMessage(hdr.ID, question)
		}
	}
	klog.V(7).Info("answer correct")
	return answer
}

func (d *DNSCacheAgent) passThrough(b []byte) ([]byte, error) {
	buf := make([]byte, maxDNSSize)
	// the dialer overrides the parameters with the upstream dns resolver
	conn, err := d.resolver.Dial(context.Background(), "network", "address")
	if err != nil {
		return buf, err
	}
	defer conn.Close()
	_, err = conn.Write(b)
	if err != nil {
		return buf, err
	}
	_ = conn.SetReadDeadline(time.Now().Add(5 * time.Second)) // golint: errcheck
	n, err := conn.Read(buf)
	if err != nil {
		klog.Infof("error on UDP connection: %v", err)
		return buf, err
	}
	return buf[:n], nil
}

// dnsErrorMessage return an encoded dns error message
func dnsErrorMessage(id uint16, rcode dnsmessage.RCode, q ...dnsmessage.Question) []byte {
	msg := dnsmessage.Message{
		Header: dnsmessage.Header{
			ID:            id,
			Response:      true,
			Authoritative: true,
			RCode:         rcode,
		},
		Questions: q,
	}
	buf, err := msg.Pack()
	if err != nil {
		klog.Errorf("SHOULD NOT HAPPEN: can not create dnsErrorMessage: %v", err)
	}
	return buf
}

func dnsTruncatedMessage(id uint16, q ...dnsmessage.Question) []byte {
	msg := dnsmessage.Message{
		Header: dnsmessage.Header{
			ID:            id,
			Response:      true,
			Authoritative: true,
			Truncated:     true,
		},
		Questions: q,
	}
	buf, err := msg.Pack()
	if err != nil {
		klog.Errorf("SHOULD NOT HAPPEN: can not create dnsTruncatedMessage: %v", err)
	}
	return buf
}

// processDNSRequest implements dnsHandlerFunc so it can be used in a DNSCache
// transforming a DNS request to the corresponding Golang Lookup functions.
// If is not able to process the request it delegates to the caller the request.
func (d *DNSCacheAgent) processDNSRequest(id uint16, q dnsmessage.Question) ([]byte, bool) {
	// DNS packet length is encoded in 2 bytes
	buf := []byte{}
	answer := dnsmessage.NewBuilder(buf,
		dnsmessage.Header{
			ID:            id,
			Response:      true,
			Authoritative: true,
		})
	answer.EnableCompression()
	err := answer.StartQuestions()
	if err != nil {
		return dnsErrorMessage(id, dnsmessage.RCodeServerFailure, q), false
	}
	answer.Question(q) // nolint: errcheck
	err = answer.StartAnswers()
	if err != nil {
		return dnsErrorMessage(id, dnsmessage.RCodeServerFailure, q), false
	}
	switch q.Type {
	case dnsmessage.TypeA:
		klog.V(7).Infof("DNS A request for %s", q.Name.String())
		addrs, err := d.lookupIP(context.Background(), "ip4", q.Name.String())
		if err != nil {
			klog.V(7).Infof("DNS A request for %s error: %v", q.Name.String(), err)
			return dnsErrorMessage(id, dnsmessage.RCodeServerFailure, q), false
		}
		if len(addrs) == 0 {
			return dnsErrorMessage(id, dnsmessage.RCodeNameError, q), false
		}
		klog.V(7).Infof("DNS A request for %s ips: %v", q.Name.String(), addrs)
		for _, ip := range addrs {
			a := ip.To4()
			if a == nil {
				continue
			}
			err = answer.AResource(
				dnsmessage.ResourceHeader{
					Name:  q.Name,
					Class: q.Class,
					TTL:   uint32(expireTimeout.Seconds()),
				},
				dnsmessage.AResource{
					A: [4]byte{a[0], a[1], a[2], a[3]},
				},
			)
			if err != nil {
				return dnsErrorMessage(id, dnsmessage.RCodeServerFailure, q), false
			}
		}
	case dnsmessage.TypeAAAA:
		klog.V(7).Infof("DNS AAAA request for %s", q.Name.String())
		addrs, err := d.lookupIP(context.Background(), "ip6", q.Name.String())
		if err != nil {
			klog.V(7).Infof("DNS AAAA request for %s error: %v", q.Name.String(), err)
			return dnsErrorMessage(id, dnsmessage.RCodeServerFailure, q), false
		}
		if len(addrs) == 0 {
			return dnsErrorMessage(id, dnsmessage.RCodeNameError, q), false
		}
		klog.V(7).Infof("DNS AAAA request for %s ips: %v", q.Name.String(), addrs)
		for _, ip := range addrs {
			if ip.To16() == nil || ip.To4() != nil {
				continue
			}
			var aaaa [16]byte
			copy(aaaa[:], ip.To16())
			err = answer.AAAAResource(
				dnsmessage.ResourceHeader{
					Name:  q.Name,
					Class: q.Class,
					TTL:   uint32(expireTimeout.Seconds()),
				},
				dnsmessage.AAAAResource{
					AAAA: aaaa,
				},
			)
			if err != nil {
				return dnsErrorMessage(id, dnsmessage.RCodeServerFailure, q), false
			}
		}
	case dnsmessage.TypePTR:
		klog.V(7).Infof("DNS PTR request for %s", q.Name.String())
		return nil, true
	case dnsmessage.TypeSRV:
		return nil, true
	case dnsmessage.TypeNS:
		return nil, true
	case dnsmessage.TypeCNAME:
		return nil, true
	case dnsmessage.TypeSOA:
		return nil, true
	case dnsmessage.TypeMX:
		return nil, true
	case dnsmessage.TypeTXT:
		return nil, true
	default:
		return nil, true
	}
	buf, err = answer.Finish()
	if err != nil {
		return dnsErrorMessage(id, dnsmessage.RCodeServerFailure, q), false
	}
	return buf, false
}

func (d *DNSCacheAgent) lookupIP(ctx context.Context, network, host string) ([]net.IP, error) {
	ips, ok := d.cache.get(network, host)
	if ok {
		klog.V(4).Infof("Cached entries for %s %s : %v", network, host, ips)
		return ips, nil
	}
	ips, err := d.resolver.LookupIP(ctx, network, host)
	if err != nil {
		// cache empty answers
		if e, ok := err.(*net.DNSError); !ok || !e.IsNotFound {
			return nil, err
		}
	}
	d.cache.add(network, host, ips)
	klog.V(4).Infof("Caching new entries for %s %s : %v", network, host, ips)
	return ips, nil
}

// https://github.com/kubernetes/kubernetes/blob/2108e54f5249c6b3b0c9f824314cb5f33c01e3f4/pkg/kubelet/network/dns/dns.go#L176
// parseResolvConf reads a resolv.conf file from the given reader, and parses
// it into nameservers, searches and options, possibly returning an error.
func parseResolvConf() (nameservers []string, searches []string, options []string, err error) {
	f, err := os.Open("/etc/resolv.conf")
	if err != nil {
		klog.ErrorS(err, "Could not open resolv conf file.")
		return nil, nil, nil, err
	}
	defer f.Close()

	file, err := utilio.ReadAtMost(f, maxResolvConfLength)
	if err != nil {
		return nil, nil, nil, err
	}

	// Lines of the form "nameserver 1.2.3.4" accumulate.
	nameservers = []string{}

	// Lines of the form "search example.com" overrule - last one wins.
	searches = []string{}

	// Lines of the form "option ndots:5 attempts:2" overrule - last one wins.
	// Each option is recorded as an element in the array.
	options = []string{}

	var allErrors []error
	lines := strings.Split(string(file), "\n")
	for l := range lines {
		trimmed := strings.TrimSpace(lines[l])
		if strings.HasPrefix(trimmed, "#") {
			continue
		}
		fields := strings.Fields(trimmed)
		if len(fields) == 0 {
			continue
		}
		if fields[0] == "nameserver" {
			if len(fields) >= 2 {
				nameservers = append(nameservers, fields[1])
			} else {
				allErrors = append(allErrors, fmt.Errorf("nameserver list is empty "))
			}
		}
		if fields[0] == "search" {
			// Normalise search fields so the same domain with and without trailing dot will only count once, to avoid hitting search validation limits.
			searches = []string{}
			for _, s := range fields[1:] {
				if s != "." {
					searches = append(searches, strings.TrimSuffix(s, "."))
				}
			}
		}
		if fields[0] == "options" {
			options = appendOptions(options, fields[1:]...)
		}
	}

	return nameservers, searches, options, utilerrors.NewAggregate(allErrors)
}

// appendOptions appends options to the given list, but does not add duplicates.
// append option will overwrite the previous one either in new line or in the same line.
func appendOptions(options []string, newOption ...string) []string {
	var optionMap = make(map[string]string)
	for _, option := range options {
		optName := strings.Split(option, ":")[0]
		optionMap[optName] = option
	}
	for _, option := range newOption {
		optName := strings.Split(option, ":")[0]
		optionMap[optName] = option
	}

	options = []string{}
	for _, v := range optionMap {
		options = append(options, v)
	}
	return options
}
