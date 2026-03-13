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

	"github.com/scionproto/scion/pkg/private/serrors"
)

type HostAddrType uint8

const (
	HostTypeNone HostAddrType = iota
	HostTypeIPv4
	HostTypeIPv6
	HostTypeSVC
)

// @ trusted
// @ requires false
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
	return fmt.Sprintf("UNKNOWN (%d)", t)
}

const (
	HostLenNone = 0
	HostLenIPv4 = net.IPv4len
	HostLenIPv6 = net.IPv6len
	HostLenSVC  = 2
)

var (
	// ErrBadHostAddrType indicates an invalid host address type.
	ErrBadHostAddrType = serrors.New("unsupported host address type")
	// ErrMalformedHostAddrType indicates a malformed host address type.
	ErrMalformedHostAddrType = serrors.New("malformed host address type")
	// ErrUnsupportedSVCAddress indicates an unsupported SVC address.
	ErrUnsupportedSVCAddress = serrors.New("unsupported SVC address")
)

const (
	SvcDS       HostSVC = 0x0001
	SvcCS       HostSVC = 0x0002
	SvcWildcard HostSVC = 0x0010
	SvcNone     HostSVC = 0xffff

	SVCMcast HostSVC = 0x8000
)

type HostAddr interface {
	// @ requires false
	Size() int
	// @ requires false
	Type() HostAddrType
	// @ requires false
	Pack() []byte
	// @ requires false
	IP() net.IP
	// @ requires false
	Copy() HostAddr
	// @ requires false
	Equal(HostAddr) bool
	// @ requires false
	String() string
}

var _ HostAddr = (HostNone)(nil)

type HostNone net.IP

// @ trusted
// @ requires false
func (h HostNone) Size() int {
	return HostLenNone
}

// @ trusted
// @ requires false
func (h HostNone) Type() HostAddrType {
	return HostTypeNone
}

// @ trusted
// @ requires false
func (h HostNone) Pack() []byte {
	return []byte{}
}

// @ trusted
// @ requires false
func (h HostNone) IP() net.IP {
	return nil
}

// @ trusted
// @ requires false
func (h HostNone) Copy() HostAddr {
	return HostNone{}
}

// @ trusted
// @ requires false
func (h HostNone) Equal(o HostAddr) bool {
	_, ok := o.(HostNone)
	return ok
}

// @ trusted
// @ requires false
func (h HostNone) String() string {
	return "<None>"
}

var _ HostAddr = (HostIPv4)(nil)

type HostIPv4 net.IP

// @ trusted
// @ requires false
func (h HostIPv4) Size() int {
	return HostLenIPv4
}

// @ trusted
// @ requires false
func (h HostIPv4) Type() HostAddrType {
	return HostTypeIPv4
}

// @ trusted
// @ requires false
func (h HostIPv4) Pack() []byte {
	return []byte(h.IP())
}

// @ trusted
// @ requires false
func (h HostIPv4) IP() net.IP {
	// XXX(kormat): ensure the reply is the 4-byte representation.
	return net.IP(h).To4()
}

// @ trusted
// @ requires false
func (h HostIPv4) Copy() HostAddr {
	return HostIPv4(append(net.IP(nil), h...))
}

// @ trusted
// @ requires false
func (h HostIPv4) Equal(o HostAddr) bool {
	ha, ok := o.(HostIPv4)
	return ok && net.IP(h).Equal(net.IP(ha))
}

// @ trusted
// @ requires false
func (h HostIPv4) String() string {
	return h.IP().String()
}

var _ HostAddr = (HostIPv6)(nil)

type HostIPv6 net.IP

// @ trusted
// @ requires false
func (h HostIPv6) Size() int {
	return HostLenIPv6
}

// @ trusted
// @ requires false
func (h HostIPv6) Type() HostAddrType {
	return HostTypeIPv6
}

// @ trusted
// @ requires false
func (h HostIPv6) Pack() []byte {
	return []byte(h)[:HostLenIPv6]
}

// @ trusted
// @ requires false
func (h HostIPv6) IP() net.IP {
	return net.IP(h)
}

// @ trusted
// @ requires false
func (h HostIPv6) Copy() HostAddr {
	return HostIPv6(append(net.IP(nil), h...))
}

// @ trusted
// @ requires false
func (h HostIPv6) Equal(o HostAddr) bool {
	ha, ok := o.(HostIPv6)
	return ok && net.IP(h).Equal(net.IP(ha))
}

// @ trusted
// @ requires false
func (h HostIPv6) String() string {
	return h.IP().String()
}

var _ HostAddr = (*HostSVC)(nil)

type HostSVC uint16

// HostSVCFromString returns the SVC address corresponding to str. For anycast
// SVC addresses, use BS_A, PS_A, CS_A, and SB_A; shorthand versions without
// the _A suffix (e.g., PS) also return anycast SVC addresses. For multicast,
// use BS_M, PS_M, CS_M, and SB_M.
// @ trusted
// @ requires false
func HostSVCFromString(str string) HostSVC {
	var m HostSVC
	switch {
	case strings.HasSuffix(str, "_A"):
		str = strings.TrimSuffix(str, "_A")
	case strings.HasSuffix(str, "_M"):
		str = strings.TrimSuffix(str, "_M")
		m = SVCMcast
	}
	switch str {
	case "DS":
		return SvcDS | m
	case "CS":
		return SvcCS | m
	case "Wildcard":
		return SvcWildcard | m
	default:
		return SvcNone
	}
}

// @ trusted
// @ requires false
func (h HostSVC) Size() int {
	return HostLenSVC
}

// @ trusted
// @ requires false
func (h HostSVC) Type() HostAddrType {
	return HostTypeSVC
}

// @ trusted
// @ requires false
func (h HostSVC) Pack() []byte {
	out := make([]byte, HostLenSVC)
	binary.BigEndian.PutUint16(out, uint16(h))
	return out
}

// @ trusted
// @ requires false
func (h HostSVC) PackWithPad(pad int) []byte {
	out := make([]byte, HostLenSVC+pad)
	binary.BigEndian.PutUint16(out, uint16(h))
	return out
}

// @ trusted
// @ requires false
func (h HostSVC) IP() net.IP {
	return nil
}

// @ trusted
// @ requires false
func (h HostSVC) IsMulticast() bool {
	return (h & SVCMcast) != 0
}

// @ trusted
// @ requires false
func (h HostSVC) Base() HostSVC {
	return h & ^SVCMcast
}

// @ trusted
// @ requires false
func (h HostSVC) Multicast() HostSVC {
	return h | SVCMcast
}

// @ trusted
// @ requires false
func (h HostSVC) Copy() HostAddr {
	return h
}

// @ trusted
// @ requires false
func (h HostSVC) Equal(o HostAddr) bool {
	ha, ok := o.(HostSVC)
	return ok && h == ha
}

// @ trusted
// @ requires false
func (h HostSVC) String() string {
	name := h.BaseString()
	cast := 'A'
	if h.IsMulticast() {
		cast = 'M'
	}
	return fmt.Sprintf("%v %c (0x%04x)", name, cast, uint16(h))
}

// BaseString returns the upper case name of the service. For hosts or unrecognized services, it
// returns UNKNOWN.
// @ trusted
// @ requires false
func (h HostSVC) BaseString() string {
	switch h.Base() {
	case SvcDS:
		return "DS"
	case SvcCS:
		return "CS"
	case SvcWildcard:
		return "Wildcard"
	default:
		return "UNKNOWN"
	}
}

// @ trusted
// @ requires false
func (h HostSVC) Network() string {
	return ""
}

// @ trusted
// @ requires false
func HostFromRaw(b []byte, htype HostAddrType) (HostAddr, error) {
	switch htype {
	case HostTypeNone:
		return HostNone{}, nil
	case HostTypeIPv4:
		if len(b) < HostLenIPv4 {
			return nil, serrors.WithCtx(ErrMalformedHostAddrType, "type", htype)
		}
		return HostIPv4(b[:HostLenIPv4]), nil
	case HostTypeIPv6:
		if len(b) < HostLenIPv6 {
			return nil, serrors.WithCtx(ErrMalformedHostAddrType, "type", htype)
		}
		return HostIPv6(b[:HostLenIPv6]), nil
	case HostTypeSVC:
		if len(b) < HostLenSVC {
			return nil, serrors.WithCtx(ErrMalformedHostAddrType, "type", htype)
		}
		return HostSVC(binary.BigEndian.Uint16(b)), nil
	default:
		return nil, serrors.WithCtx(ErrBadHostAddrType, "type", htype)
	}
}

// @ trusted
// @ requires false
func HostFromIP(ip net.IP) HostAddr {
	if ip4 := ip.To4(); ip4 != nil {
		return HostIPv4(ip4)
	}
	return HostIPv6(ip)
}

// @ trusted
// @ requires false
func HostFromIPStr(s string) HostAddr {
	ip := net.ParseIP(s)
	if ip == nil {
		return nil
	}
	return HostFromIP(ip)
}

// @ trusted
// @ requires false
func HostLen(htype HostAddrType) (uint8, error) {
	var length uint8
	switch htype {
	case HostTypeNone:
		length = HostLenNone
	case HostTypeIPv4:
		length = HostLenIPv4
	case HostTypeIPv6:
		length = HostLenIPv6
	case HostTypeSVC:
		length = HostLenSVC
	default:
		return 0, serrors.WithCtx(ErrBadHostAddrType, "type", htype)
	}
	return length, nil
}

// @ trusted
// @ requires false
func HostTypeCheck(t HostAddrType) bool {
	switch t {
	case HostTypeIPv6, HostTypeIPv4, HostTypeSVC:
		return true
	}
	return false
}
