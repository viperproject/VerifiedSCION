package addr

func TestHostFromRaw() {}
func TestHostFromRaw_short_IPv6(b_HostFromRaw []byte, htype_HostFromRaw HostAddrType) {
	var tmp_b_HostFromRaw []byte
	var tmp_htype_HostFromRaw HostAddrType
	tmp_b_HostFromRaw = []byte{0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}
	tmp_htype_HostFromRaw = 0x2
	// @ inhale acc(b_HostFromRaw)
	// @ inhale isValidHostAddrType(htype_HostFromRaw)
	// @ inhale len(b_HostFromRaw) == sizeOfHostAddrType(htype_HostFromRaw)
	// @ assume b_HostFromRaw === tmp_b_HostFromRaw
	// @ assume htype_HostFromRaw == tmp_htype_HostFromRaw
	res, err := HostFromRaw(tmp_b_HostFromRaw, tmp_htype_HostFromRaw)
	// @ assert err != nil
	// @ assert nil == res
}
func TestHostFromRaw_valid_IPv6(b_HostFromRaw []byte, htype_HostFromRaw HostAddrType) {
	var tmp_b_HostFromRaw []byte
	var tmp_htype_HostFromRaw HostAddrType
	tmp_b_HostFromRaw = []byte{0xde, 0xad, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0xbe, 0xef}
	tmp_htype_HostFromRaw = 0x2
	// @ inhale acc(b_HostFromRaw)
	// @ inhale isValidHostAddrType(htype_HostFromRaw)
	// @ inhale len(b_HostFromRaw) == sizeOfHostAddrType(htype_HostFromRaw)
	// @ assume b_HostFromRaw === tmp_b_HostFromRaw
	// @ assume htype_HostFromRaw == tmp_htype_HostFromRaw
	// @ refute false
	res, err := HostFromRaw(tmp_b_HostFromRaw, tmp_htype_HostFromRaw)
	// @ assert err == nil
	expected := HostIPv6{0xde, 0xad, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0xbe, 0xef}
	equal := res.Equal(expected)
	// @ assert equal
}
func TestHostFromRaw_nil_SVC(b_HostFromRaw []byte, htype_HostFromRaw HostAddrType) {
	var tmp_b_HostFromRaw []byte
	var tmp_htype_HostFromRaw HostAddrType
	tmp_b_HostFromRaw = []byte(nil)
	tmp_htype_HostFromRaw = 0x3
	// @ inhale acc(b_HostFromRaw)
	// @ inhale isValidHostAddrType(htype_HostFromRaw)
	// @ inhale len(b_HostFromRaw) == sizeOfHostAddrType(htype_HostFromRaw)
	// @ assume b_HostFromRaw === tmp_b_HostFromRaw
	// @ assume htype_HostFromRaw == tmp_htype_HostFromRaw
	res, err := HostFromRaw(tmp_b_HostFromRaw, tmp_htype_HostFromRaw)
	// @ assert err != nil
	// @ assert nil == res
}
func TestHostFromRaw_valid_SVC(b_HostFromRaw []byte, htype_HostFromRaw HostAddrType) {
	var tmp_b_HostFromRaw []byte
	var tmp_htype_HostFromRaw HostAddrType
	tmp_b_HostFromRaw = []byte{0x0, 0x1}
	tmp_htype_HostFromRaw = 0x3
	// @ inhale acc(b_HostFromRaw)
	// @ inhale isValidHostAddrType(htype_HostFromRaw)
	// @ inhale len(b_HostFromRaw) == sizeOfHostAddrType(htype_HostFromRaw)
	// @ assume b_HostFromRaw === tmp_b_HostFromRaw
	// @ assume htype_HostFromRaw == tmp_htype_HostFromRaw
	// @ refute false
	res, err := HostFromRaw(tmp_b_HostFromRaw, tmp_htype_HostFromRaw)
	// @ assert err == nil
	var expected HostSVC = 0x1
	equal := res.Equal(expected)
	// @ assert equal
}
func TestHostFromRaw_nil_IPv4(b_HostFromRaw []byte, htype_HostFromRaw HostAddrType) {
	var tmp_b_HostFromRaw []byte
	var tmp_htype_HostFromRaw HostAddrType
	tmp_b_HostFromRaw = []byte(nil)
	tmp_htype_HostFromRaw = 0x1
	// @ inhale acc(b_HostFromRaw)
	// @ inhale isValidHostAddrType(htype_HostFromRaw)
	// @ inhale len(b_HostFromRaw) == sizeOfHostAddrType(htype_HostFromRaw)
	// @ assume b_HostFromRaw === tmp_b_HostFromRaw
	// @ assume htype_HostFromRaw == tmp_htype_HostFromRaw
	res, err := HostFromRaw(tmp_b_HostFromRaw, tmp_htype_HostFromRaw)
	// @ assert err != nil
	// @ assert nil == res
}
func TestHostFromRaw_short_IPv4(b_HostFromRaw []byte, htype_HostFromRaw HostAddrType) {
	var tmp_b_HostFromRaw []byte
	var tmp_htype_HostFromRaw HostAddrType
	tmp_b_HostFromRaw = []byte{0x0, 0x0, 0x0}
	tmp_htype_HostFromRaw = 0x1
	// @ inhale acc(b_HostFromRaw)
	// @ inhale isValidHostAddrType(htype_HostFromRaw)
	// @ inhale len(b_HostFromRaw) == sizeOfHostAddrType(htype_HostFromRaw)
	// @ assume b_HostFromRaw === tmp_b_HostFromRaw
	// @ assume htype_HostFromRaw == tmp_htype_HostFromRaw
	res, err := HostFromRaw(tmp_b_HostFromRaw, tmp_htype_HostFromRaw)
	// @ assert err != nil
	// @ assert nil == res
}
func TestHostFromRaw_valid_IPv4(b_HostFromRaw []byte, htype_HostFromRaw HostAddrType) {
	var tmp_b_HostFromRaw []byte
	var tmp_htype_HostFromRaw HostAddrType
	tmp_b_HostFromRaw = []byte{0x7f, 0x0, 0x0, 0x1}
	tmp_htype_HostFromRaw = 0x1
	// @ inhale acc(b_HostFromRaw)
	// @ inhale isValidHostAddrType(htype_HostFromRaw)
	// @ inhale len(b_HostFromRaw) == sizeOfHostAddrType(htype_HostFromRaw)
	// @ assume b_HostFromRaw === tmp_b_HostFromRaw
	// @ assume htype_HostFromRaw == tmp_htype_HostFromRaw
	// @ refute false
	res, err := HostFromRaw(tmp_b_HostFromRaw, tmp_htype_HostFromRaw)
	// @ assert err == nil
	expected := HostIPv4{0x7f, 0x0, 0x0, 0x1}
	equal := res.Equal(expected)
	// @ assert equal
}
func TestHostFromRaw_nil_IPv6(b_HostFromRaw []byte, htype_HostFromRaw HostAddrType) {
	var tmp_b_HostFromRaw []byte
	var tmp_htype_HostFromRaw HostAddrType
	tmp_b_HostFromRaw = []byte(nil)
	tmp_htype_HostFromRaw = 0x2
	// @ inhale acc(b_HostFromRaw)
	// @ inhale isValidHostAddrType(htype_HostFromRaw)
	// @ inhale len(b_HostFromRaw) == sizeOfHostAddrType(htype_HostFromRaw)
	// @ assume b_HostFromRaw === tmp_b_HostFromRaw
	// @ assume htype_HostFromRaw == tmp_htype_HostFromRaw
	res, err := HostFromRaw(tmp_b_HostFromRaw, tmp_htype_HostFromRaw)
	// @ assert err != nil
	// @ assert nil == res
}
func TestHostFromRaw_short_SVC(b_HostFromRaw []byte, htype_HostFromRaw HostAddrType) {
	var tmp_b_HostFromRaw []byte
	var tmp_htype_HostFromRaw HostAddrType
	tmp_b_HostFromRaw = []byte{0x0}
	tmp_htype_HostFromRaw = 0x3
	// @ inhale acc(b_HostFromRaw)
	// @ inhale isValidHostAddrType(htype_HostFromRaw)
	// @ inhale len(b_HostFromRaw) == sizeOfHostAddrType(htype_HostFromRaw)
	// @ assume b_HostFromRaw === tmp_b_HostFromRaw
	// @ assume htype_HostFromRaw == tmp_htype_HostFromRaw
	res, err := HostFromRaw(tmp_b_HostFromRaw, tmp_htype_HostFromRaw)
	// @ assert err != nil
	// @ assert nil == res
}
