// Copyright 2016 ETH Zurich
// Copyright 2018 ETH Zurich, Anapaya Systems
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//   http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

// +gobra
package addr

import (
	"encoding/binary"
	"fmt"
	"net"
	"strings"

	//"github.com/scionproto/scion/pkg/private/serrors"
	"serrors"
)

type HostAddrType uint8

//const (
//	HostTypeNone HostAddrType = iota
//	HostTypeIPv4										
//	HostTypeIPv6										
//	HostTypeSVC											
//)

const (
	HostTypeNone HostAddrType = 0
	HostTypeIPv4 HostAddrType = 1
	HostTypeIPv6 HostAddrType = 2
	HostTypeSVC  HostAddrType = 3
)

//@ decreases
func (t HostAddrType) String() string {
	switch t {
	case HostTypeNone:
		return "None"
	case HostTypeIPv4:
		return "IPv4"
	case HostTypeIPv6:
		return "IPv6"
	case HostTypeSVC:
		return "SVC"
	}
	//(dionisis) This will fail since sprintf currently expects a primitive type
	//return fmt.Sprintf("UNKNOWN (%d)", t)
	return fmt.Sprintf("UNKNOWN (%d)", uint8(t)) //rewritten version
}

const (
	HostLenNone = 0
	HostLenIPv4 = net.IPv4len
	HostLenIPv6 = net.IPv6len
	HostLenSVC  = 2
)

// (VerifiedSCION) The following variables are not mutated by any functions so
//they are replaced by functions until we have support for globals

//var (
//	// ErrBadHostAddrType indicates an invalid host address type.
//	ErrBadHostAddrType = serrors.New("unsupported host address type")
//	// ErrMalformedHostAddrType indicates a malformed host address type.
//	ErrMalformedHostAddrType = serrors.New("malformed host address type")
//	// ErrUnsupportedSVCAddress indicates an unsupported SVC address.
//	ErrUnsupportedSVCAddress = serrors.New("unsupported SVC address")
//)

func ErrBadHostAddrType () error {
	return serrors.New("unsupported host address type")
}

func ErrMalformedHostAddrType () error {
	return serrors.New("malformed host address type")
}

func ErrUnsupportedSVCAddress () error {
	return serrors.New("unsupported SVC address")
}

const (
	SvcDS       HostSVC = 0x0001
	SvcCS       HostSVC = 0x0002
	SvcWildcard HostSVC = 0x0010
	SvcNone     HostSVC = 0xffff

	SVCMcast HostSVC = 0x8000
)

type HostAddr interface {
	//@ pred Mem()

	//@ preserves acc(Mem(), 1/10000)
	//@ decreases
	Size() int

	//@ preserves acc(Mem(), 1/10000)
	//@ decreases
	Type() HostAddrType

	//@ requires acc(Mem(), 1/10000)
	//@ ensures acc(res, 1/10000)
	Pack() (res []byte)

	//@ requires acc(Mem(), 1/10000)
	//@ ensures acc(res, 1/10000)
	IP() (res net.IP)

	//@ preserves acc(Mem(), 1/10000)
	//@ ensures res.Mem()
	Copy() (res HostAddr)

	//@ preserves acc(Mem(), 1/10000) && acc(o.Mem(), 1/10000)
	Equal(o HostAddr) bool
	
	// (VerifiedSCION) Can't use imported types as interface fields yet
	// replaced by the String() method which is the one that should be implemented
	//fmt.Stringer

	//@ preserves acc(Mem())
	//@ decreases
	String() string
}

// (VerifiedSCION) Replaced with implementation proof in host.gobra
//var _ HostAddr = (HostNone)(nil)

type HostNone net.IP

//@ decreases
func (h HostNone) Size() int {
	return HostLenNone
}

//@ decreases
func (h HostNone) Type() HostAddrType {
	return HostTypeNone
}

//@ ensures acc(res)
//@ decreases
func (h HostNone) Pack() (res []byte) {
	return []byte{}
}

//@ ensures acc(res)
//@ decreases
func (h HostNone) IP() (res net.IP) {
	return nil
}

//@ preserves acc(h.Mem(), 1/10000)
//@ ensures res.Mem()
//@ decreases
func (h HostNone) Copy() (res HostAddr) {
	//(VerifiedSCION) introduce tmp
	tmp := HostNone{}
	//@ fold tmp.Mem()
	return tmp
	//return HostNone{}
}

//@ decreases
func (h HostNone) Equal(o HostAddr) bool {
	_, ok := o.(HostNone)
	return ok
}

//@decreases
func (h HostNone) String() string {
	return "<None>"
}

// (VerifiedSCION) Replaced with implementation proof in host.gobra
//var _ HostAddr = (HostIPv4)(nil)

type HostIPv4 net.IP

//@ preserves acc(h.Mem(), 1/10000)
//@ decreases
func (h HostIPv4) Size() int {
	return HostLenIPv4
}

//@ preserves acc(h.Mem(), 1/10000)
//@ decreases
func (h HostIPv4) Type() HostAddrType {
	return HostTypeIPv4
}

//@ requires acc(h.Mem(), 1/10000)
//@ ensures acc(res, 1/10000)
//@ decreases
func (h HostIPv4) Pack() (res []byte) {
	return []byte(h.IP())
}

//@ requires acc(h.Mem(), 1/10000)
//@ ensures acc(res, 1/10000)
//@ decreases
func (h HostIPv4) IP() (res net.IP) {
	// XXX(kormat): ensure the reply is the 4-byte representation.
	//@ unfold acc(h.Mem(), 1/10000)
	return net.IP(h).To4()
}

//@ preserves acc(h.Mem(), 1/10000)
//@ ensures acc(res.Mem())
//@ decreases
func (h HostIPv4) Copy() (res HostAddr) {
	var tmp HostIPv4 = HostIPv4(append(net.IP(nil), h...))
	//@ fold tmp.Mem()
	return tmp
}

//@ preserves acc(h.Mem(), 1/10000)
//@ preserves acc(o.Mem(), 1/10000)
//@ decreases
func (h HostIPv4) Equal(o HostAddr) bool {
	ha, ok := o.(HostIPv4)
	return ok && net.IP(h).Equal(net.IP(ha))
}

//@ preserves acc(h.Mem(), 1/10000)
//@ decreases
func (h HostIPv4) String() string {
	return h.IP().String()
}

//var _ HostAddr = (HostIPv6)(nil)
//
//type HostIPv6 net.IP
//
//func (h HostIPv6) Size() int {
//	return HostLenIPv6
//}
//
//func (h HostIPv6) Type() HostAddrType {
//	return HostTypeIPv6
//}
//
//func (h HostIPv6) Pack() []byte {
//	return []byte(h)[:HostLenIPv6]
//}
//
//func (h HostIPv6) IP() net.IP {
//	return net.IP(h)
//}
//
//func (h HostIPv6) Copy() HostAddr {
//	return HostIPv6(append(net.IP(nil), h...))
//}
//
//func (h HostIPv6) Equal(o HostAddr) bool {
//	ha, ok := o.(HostIPv6)
//	return ok && net.IP(h).Equal(net.IP(ha))
//}
//
//func (h HostIPv6) String() string {
//	return h.IP().String()
//}
//
//var _ HostAddr = (*HostSVC)(nil)
//
type HostSVC uint16
//
//// HostSVCFromString returns the SVC address corresponding to str. For anycast
//// SVC addresses, use BS_A, PS_A, CS_A, and SB_A; shorthand versions without
//// the _A suffix (e.g., PS) also return anycast SVC addresses. For multicast,
//// use BS_M, PS_M, CS_M, and SB_M.
//func HostSVCFromString(str string) HostSVC {
//	var m HostSVC
//	switch {
//	case strings.HasSuffix(str, "_A"):
//		str = strings.TrimSuffix(str, "_A")
//	case strings.HasSuffix(str, "_M"):
//		str = strings.TrimSuffix(str, "_M")
//		m = SVCMcast
//	}
//	switch str {
//	case "DS":
//		return SvcDS | m
//	case "CS":
//		return SvcCS | m
//	case "Wildcard":
//		return SvcWildcard | m
//	default:
//		return SvcNone
//	}
//}
//
//func (h HostSVC) Size() int {
//	return HostLenSVC
//}
//
//func (h HostSVC) Type() HostAddrType {
//	return HostTypeSVC
//}
//
//func (h HostSVC) Pack() []byte {
//	out := make([]byte, HostLenSVC)
//	binary.BigEndian.PutUint16(out, uint16(h))
//	return out
//}
//
//func (h HostSVC) PackWithPad(pad int) []byte {
//	out := make([]byte, HostLenSVC+pad)
//	binary.BigEndian.PutUint16(out, uint16(h))
//	return out
//}
//
//func (h HostSVC) IP() net.IP {
//	return nil
//}
//
//func (h HostSVC) IsMulticast() bool {
//	return (h & SVCMcast) != 0
//}
//
//func (h HostSVC) Base() HostSVC {
//	return h & ^SVCMcast
//}
//
//func (h HostSVC) Multicast() HostSVC {
//	return h | SVCMcast
//}
//
//func (h HostSVC) Copy() HostAddr {
//	return h
//}
//
//func (h HostSVC) Equal(o HostAddr) bool {
//	ha, ok := o.(HostSVC)
//	return ok && h == ha
//}
//
//func (h HostSVC) String() string {
//	name := h.BaseString()
//	cast := 'A'
//	if h.IsMulticast() {
//		cast = 'M'
//	}
//	return fmt.Sprintf("%v %c (0x%04x)", name, cast, uint16(h))
//}
//
//// BaseString returns the upper case name of the service. For hosts or unrecognized services, it
//// returns UNKNOWN.
//func (h HostSVC) BaseString() string {
//	switch h.Base() {
//	case SvcDS:
//		return "DS"
//	case SvcCS:
//		return "CS"
//	case SvcWildcard:
//		return "Wildcard"
//	default:
//		return "UNKNOWN"
//	}
//}
//
//func (h HostSVC) Network() string {
//	return ""
//}
//
//func HostFromRaw(b []byte, htype HostAddrType) (HostAddr, error) {
//	switch htype {
//	case HostTypeNone:
//		return HostNone{}, nil
//	case HostTypeIPv4:
//		if len(b) < HostLenIPv4 {
//			return nil, serrors.WithCtx(ErrMalformedHostAddrType, "type", htype)
//		}
//		return HostIPv4(b[:HostLenIPv4]), nil
//	case HostTypeIPv6:
//		if len(b) < HostLenIPv6 {
//			return nil, serrors.WithCtx(ErrMalformedHostAddrType, "type", htype)
//		}
//		return HostIPv6(b[:HostLenIPv6]), nil
//	case HostTypeSVC:
//		if len(b) < HostLenSVC {
//			return nil, serrors.WithCtx(ErrMalformedHostAddrType, "type", htype)
//		}
//		return HostSVC(binary.BigEndian.Uint16(b)), nil
//	default:
//		return nil, serrors.WithCtx(ErrBadHostAddrType, "type", htype)
//	}
//}
//
//func HostFromIP(ip net.IP) HostAddr {
//	if ip4 := ip.To4(); ip4 != nil {
//		return HostIPv4(ip4)
//	}
//	return HostIPv6(ip)
//}
//
//func HostFromIPStr(s string) HostAddr {
//	ip := net.ParseIP(s)
//	if ip == nil {
//		return nil
//	}
//	return HostFromIP(ip)
//}
//
//func HostLen(htype HostAddrType) (uint8, error) {
//	var length uint8
//	switch htype {
//	case HostTypeNone:
//		length = HostLenNone
//	case HostTypeIPv4:
//		length = HostLenIPv4
//	case HostTypeIPv6:
//		length = HostLenIPv6
//	case HostTypeSVC:
//		length = HostLenSVC
//	default:
//		return 0, serrors.WithCtx(ErrBadHostAddrType, "type", htype)
//	}
//	return length, nil
//}
//
//func HostTypeCheck(t HostAddrType) bool {
//	switch t {
//	case HostTypeIPv6, HostTypeIPv4, HostTypeSVC:
//		return true
//	}
//	return false
//}
//
