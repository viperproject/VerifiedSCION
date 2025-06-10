package addr

import (
	// @ . "github.com/scionproto/scion/verification/utils/definitions"
	// @ sl "github.com/scionproto/scion/verification/utils/slices"
	"fmt"
	"github.com/scionproto/scion/assertion"
)

func TestHostFromRaw_valid_SVC(b_HostFromRaw []byte, htype_HostFromRaw HostAddrType) {
	var tmp_b_HostFromRaw []byte
	var tmp_htype_HostFromRaw HostAddrType
	tmp_b_HostFromRaw = []uint8{0x0, 0x1}
	tmp_htype_HostFromRaw = 3
	// @ inhale acc(b_HostFromRaw)
	// @ inhale isValidHostAddrType(htype_HostFromRaw)
	// @ inhale len(b_HostFromRaw) == sizeOfHostAddrType(htype_HostFromRaw)
	// @ assume b_HostFromRaw === tmp_b_HostFromRaw
	// @ assume htype_HostFromRaw == tmp_htype_HostFromRaw
	// @ refute false
	res, err := HostFromRaw(b_HostFromRaw, htype_HostFromRaw)
	// @ ass0_HostFromRaw := err == nil
	// @ assert ass0_HostFromRaw
	var expected = HostSVC(0x1)
	// @ ass1_HostFromRaw := res.Equal(expected)
	// @ assert ass1_HostFromRaw
}
func TestHostFromRaw_short_IPv4(b_HostFromRaw []byte, htype_HostFromRaw HostAddrType) {
	var tmp_b_HostFromRaw []byte
	var tmp_htype_HostFromRaw HostAddrType
	tmp_b_HostFromRaw = []uint8{0x0, 0x0, 0x0}
	tmp_htype_HostFromRaw = 1
	// @ inhale acc(b_HostFromRaw)
	// @ inhale isValidHostAddrType(htype_HostFromRaw)
	// @ inhale len(b_HostFromRaw) == sizeOfHostAddrType(htype_HostFromRaw)
	// @ assume b_HostFromRaw === tmp_b_HostFromRaw
	// @ assume htype_HostFromRaw == tmp_htype_HostFromRaw
	res, err := HostFromRaw(b_HostFromRaw, htype_HostFromRaw)
	// @ ass0_HostFromRaw := err != nil
	// @ assert ass0_HostFromRaw
	// @ ass1_HostFromRaw := nil == res
	// @ assert ass1_HostFromRaw
}
func TestHostFromRaw_nil_IPv6(b_HostFromRaw []byte, htype_HostFromRaw HostAddrType) {
	var tmp_b_HostFromRaw []byte
	var tmp_htype_HostFromRaw HostAddrType
	tmp_b_HostFromRaw = []uint8(nil)
	tmp_htype_HostFromRaw = 2
	// @ inhale acc(b_HostFromRaw)
	// @ inhale isValidHostAddrType(htype_HostFromRaw)
	// @ inhale len(b_HostFromRaw) == sizeOfHostAddrType(htype_HostFromRaw)
	// @ assume b_HostFromRaw === tmp_b_HostFromRaw
	// @ assume htype_HostFromRaw == tmp_htype_HostFromRaw
	res, err := HostFromRaw(b_HostFromRaw, htype_HostFromRaw)
	// @ ass0_HostFromRaw := err != nil
	// @ assert ass0_HostFromRaw
	// @ ass1_HostFromRaw := nil == res
	// @ assert ass1_HostFromRaw
}
func TestHostFromRaw_valid_IPv6(b_HostFromRaw []byte, htype_HostFromRaw HostAddrType) {
	var tmp_b_HostFromRaw []byte
	var tmp_htype_HostFromRaw HostAddrType
	tmp_b_HostFromRaw = []uint8{0xde, 0xad, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0xbe, 0xef}
	tmp_htype_HostFromRaw = 2
	// @ inhale acc(b_HostFromRaw)
	// @ inhale isValidHostAddrType(htype_HostFromRaw)
	// @ inhale len(b_HostFromRaw) == sizeOfHostAddrType(htype_HostFromRaw)
	// @ assume b_HostFromRaw === tmp_b_HostFromRaw
	// @ assume htype_HostFromRaw == tmp_htype_HostFromRaw
	// @ refute false
	res, err := HostFromRaw(b_HostFromRaw, htype_HostFromRaw)
	// @ ass0_HostFromRaw := err == nil
	// @ assert ass0_HostFromRaw
	var expected = HostIPv6{0xde, 0xad, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0xbe, 0xef}
	// @ ass1_HostFromRaw := res.Equal(expected)
	// @ assert ass1_HostFromRaw
}
func TestHostFromRaw_nil_SVC(b_HostFromRaw []byte, htype_HostFromRaw HostAddrType) {
	var tmp_b_HostFromRaw []byte
	var tmp_htype_HostFromRaw HostAddrType
	tmp_b_HostFromRaw = []uint8(nil)
	tmp_htype_HostFromRaw = 3
	// @ inhale acc(b_HostFromRaw)
	// @ inhale isValidHostAddrType(htype_HostFromRaw)
	// @ inhale len(b_HostFromRaw) == sizeOfHostAddrType(htype_HostFromRaw)
	// @ assume b_HostFromRaw === tmp_b_HostFromRaw
	// @ assume htype_HostFromRaw == tmp_htype_HostFromRaw
	res, err := HostFromRaw(b_HostFromRaw, htype_HostFromRaw)
	// @ ass0_HostFromRaw := err != nil
	// @ assert ass0_HostFromRaw
	// @ ass1_HostFromRaw := nil == res
	// @ assert ass1_HostFromRaw
}
func TestHostFromRaw_nil_IPv4(b_HostFromRaw []byte, htype_HostFromRaw HostAddrType) {
	var tmp_b_HostFromRaw []byte
	var tmp_htype_HostFromRaw HostAddrType
	tmp_b_HostFromRaw = []uint8(nil)
	tmp_htype_HostFromRaw = 1
	// @ inhale acc(b_HostFromRaw)
	// @ inhale isValidHostAddrType(htype_HostFromRaw)
	// @ inhale len(b_HostFromRaw) == sizeOfHostAddrType(htype_HostFromRaw)
	// @ assume b_HostFromRaw === tmp_b_HostFromRaw
	// @ assume htype_HostFromRaw == tmp_htype_HostFromRaw
	res, err := HostFromRaw(b_HostFromRaw, htype_HostFromRaw)
	// @ ass0_HostFromRaw := err != nil
	// @ assert ass0_HostFromRaw
	// @ ass1_HostFromRaw := nil == res
	// @ assert ass1_HostFromRaw
}
func TestHostFromRaw_valid_IPv4(b_HostFromRaw []byte, htype_HostFromRaw HostAddrType) {
	var tmp_b_HostFromRaw []byte
	var tmp_htype_HostFromRaw HostAddrType
	tmp_b_HostFromRaw = []uint8{0x7f, 0x0, 0x0, 0x1}
	tmp_htype_HostFromRaw = 1
	// @ inhale acc(b_HostFromRaw)
	// @ inhale isValidHostAddrType(htype_HostFromRaw)
	// @ inhale len(b_HostFromRaw) == sizeOfHostAddrType(htype_HostFromRaw)
	// @ assume b_HostFromRaw === tmp_b_HostFromRaw
	// @ assume htype_HostFromRaw == tmp_htype_HostFromRaw
	// @ refute false
	res, err := HostFromRaw(b_HostFromRaw, htype_HostFromRaw)
	// @ ass0_HostFromRaw := err == nil
	// @ assert ass0_HostFromRaw
	var expected = HostIPv4{0x7f, 0x0, 0x0, 0x1}
	// @ ass1_HostFromRaw := res.Equal(expected)
	// @ assert ass1_HostFromRaw
}
func TestHostFromRaw_short_IPv6(b_HostFromRaw []byte, htype_HostFromRaw HostAddrType) {
	var tmp_b_HostFromRaw []byte
	var tmp_htype_HostFromRaw HostAddrType
	tmp_b_HostFromRaw = []uint8{0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}
	tmp_htype_HostFromRaw = 2
	// @ inhale acc(b_HostFromRaw)
	// @ inhale isValidHostAddrType(htype_HostFromRaw)
	// @ inhale len(b_HostFromRaw) == sizeOfHostAddrType(htype_HostFromRaw)
	// @ assume b_HostFromRaw === tmp_b_HostFromRaw
	// @ assume htype_HostFromRaw == tmp_htype_HostFromRaw
	res, err := HostFromRaw(b_HostFromRaw, htype_HostFromRaw)
	// @ ass0_HostFromRaw := err != nil
	// @ assert ass0_HostFromRaw
	// @ ass1_HostFromRaw := nil == res
	// @ assert ass1_HostFromRaw
}
func TestHostFromRaw_short_SVC(b_HostFromRaw []byte, htype_HostFromRaw HostAddrType) {
	var tmp_b_HostFromRaw []byte
	var tmp_htype_HostFromRaw HostAddrType
	tmp_b_HostFromRaw = []uint8{0x0}
	tmp_htype_HostFromRaw = 3
	// @ inhale acc(b_HostFromRaw)
	// @ inhale isValidHostAddrType(htype_HostFromRaw)
	// @ inhale len(b_HostFromRaw) == sizeOfHostAddrType(htype_HostFromRaw)
	// @ assume b_HostFromRaw === tmp_b_HostFromRaw
	// @ assume htype_HostFromRaw == tmp_htype_HostFromRaw
	res, err := HostFromRaw(b_HostFromRaw, htype_HostFromRaw)
	// @ ass0_HostFromRaw := err != nil
	// @ assert ass0_HostFromRaw
	// @ ass1_HostFromRaw := nil == res
	// @ assert ass1_HostFromRaw
}
