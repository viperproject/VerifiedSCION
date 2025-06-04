package addr

func TestParseAS() {}
func TestParseAS__00(_as_ParseAS string) {
	var tmp__as_ParseAS string
	tmp__as_ParseAS = ""
	// @ assume _as_ParseAS == tmp__as_ParseAS
	retAs, err := ParseAS(tmp__as_ParseAS)
	// @ assert err != nil
}
func TestParseAS_0(_as_ParseAS string) {
	var tmp__as_ParseAS string
	tmp__as_ParseAS = "0"
	// @ assume _as_ParseAS == tmp__as_ParseAS
	// @ refute false
	retAs, err := ParseAS(tmp__as_ParseAS)
	// @ assert err == nil
	// @ assert err == nil
	// @ assert 0x0 == retAs
}
func TestParseAS_0x0(_as_ParseAS string) {
	var tmp__as_ParseAS string
	tmp__as_ParseAS = "0x0"
	// @ assume _as_ParseAS == tmp__as_ParseAS
	retAs, err := ParseAS(tmp__as_ParseAS)
	// @ assert err != nil
}
func TestParseAS_ff(_as_ParseAS string) {
	var tmp__as_ParseAS string
	tmp__as_ParseAS = "ff"
	// @ assume _as_ParseAS == tmp__as_ParseAS
	retAs, err := ParseAS(tmp__as_ParseAS)
	// @ assert err != nil
}
func TestParseAS_1(_as_ParseAS string) {
	var tmp__as_ParseAS string
	tmp__as_ParseAS = "1"
	// @ assume _as_ParseAS == tmp__as_ParseAS
	// @ refute false
	retAs, err := ParseAS(tmp__as_ParseAS)
	// @ assert err == nil
	// @ assert err == nil
	// @ assert 0x1 == retAs
}
func TestParseAS_4294967295(_as_ParseAS string) {
	var tmp__as_ParseAS string
	tmp__as_ParseAS = "4294967295"
	// @ assume _as_ParseAS == tmp__as_ParseAS
	// @ refute false
	retAs, err := ParseAS(tmp__as_ParseAS)
	// @ assert err == nil
	// @ assert err == nil
	// @ assert 0xffffffff == retAs
}
func TestParseAS_4294967296(_as_ParseAS string) {
	var tmp__as_ParseAS string
	tmp__as_ParseAS = "4294967296"
	// @ assume _as_ParseAS == tmp__as_ParseAS
	retAs, err := ParseAS(tmp__as_ParseAS)
	// @ assert err != nil
}
func TestParseAS__(_as_ParseAS string) {
	var tmp__as_ParseAS string
	tmp__as_ParseAS = ":"
	// @ assume _as_ParseAS == tmp__as_ParseAS
	retAs, err := ParseAS(tmp__as_ParseAS)
	// @ assert err != nil
}
func TestParseAS_0_0_0(_as_ParseAS string) {
	var tmp__as_ParseAS string
	tmp__as_ParseAS = "0:0:0"
	// @ assume _as_ParseAS == tmp__as_ParseAS
	// @ refute false
	retAs, err := ParseAS(tmp__as_ParseAS)
	// @ assert err == nil
	// @ assert err == nil
	// @ assert 0x0 == retAs
}
func TestParseAS_0_0_0_(_as_ParseAS string) {
	var tmp__as_ParseAS string
	tmp__as_ParseAS = "0:0:0:"
	// @ assume _as_ParseAS == tmp__as_ParseAS
	retAs, err := ParseAS(tmp__as_ParseAS)
	// @ assert err != nil
}
func TestParseAS__0_0_(_as_ParseAS string) {
	var tmp__as_ParseAS string
	tmp__as_ParseAS = ":0:0:"
	// @ assume _as_ParseAS == tmp__as_ParseAS
	retAs, err := ParseAS(tmp__as_ParseAS)
	// @ assert err != nil
}
func TestParseAS_0_0(_as_ParseAS string) {
	var tmp__as_ParseAS string
	tmp__as_ParseAS = "0:0"
	// @ assume _as_ParseAS == tmp__as_ParseAS
	retAs, err := ParseAS(tmp__as_ParseAS)
	// @ assert err != nil
}
func TestParseAS_0_0_1(_as_ParseAS string) {
	var tmp__as_ParseAS string
	tmp__as_ParseAS = "0:0:1"
	// @ assume _as_ParseAS == tmp__as_ParseAS
	// @ refute false
	retAs, err := ParseAS(tmp__as_ParseAS)
	// @ assert err == nil
	// @ assert err == nil
	// @ assert 0x1 == retAs
}
func TestParseAS_1_0_0(_as_ParseAS string) {
	var tmp__as_ParseAS string
	tmp__as_ParseAS = "1:0:0"
	// @ assume _as_ParseAS == tmp__as_ParseAS
	// @ refute false
	retAs, err := ParseAS(tmp__as_ParseAS)
	// @ assert err == nil
	// @ assert err == nil
	// @ assert 0x100000000 == retAs
}
func TestParseAS_ffff_ffff_ffff(_as_ParseAS string) {
	var tmp__as_ParseAS string
	tmp__as_ParseAS = "ffff:ffff:ffff"
	// @ assume _as_ParseAS == tmp__as_ParseAS
	// @ refute false
	retAs, err := ParseAS(tmp__as_ParseAS)
	// @ assert err == nil
	// @ assert err == nil
	// @ assert 0xffffffffffff == retAs
}
func TestParseAS_10000_0_0(_as_ParseAS string) {
	var tmp__as_ParseAS string
	tmp__as_ParseAS = "10000:0:0"
	// @ assume _as_ParseAS == tmp__as_ParseAS
	retAs, err := ParseAS(tmp__as_ParseAS)
	// @ assert err != nil
}
func TestParseAS_0_10000_0(_as_ParseAS string) {
	var tmp__as_ParseAS string
	tmp__as_ParseAS = "0:10000:0"
	// @ assume _as_ParseAS == tmp__as_ParseAS
	retAs, err := ParseAS(tmp__as_ParseAS)
	// @ assert err != nil
}
func TestParseAS_0_0_10000(_as_ParseAS string) {
	var tmp__as_ParseAS string
	tmp__as_ParseAS = "0:0:10000"
	// @ assume _as_ParseAS == tmp__as_ParseAS
	retAs, err := ParseAS(tmp__as_ParseAS)
	// @ assert err != nil
}
func TestParseAS_0_0x0_0(_as_ParseAS string) {
	var tmp__as_ParseAS string
	tmp__as_ParseAS = "0:0x0:0"
	// @ assume _as_ParseAS == tmp__as_ParseAS
	retAs, err := ParseAS(tmp__as_ParseAS)
	// @ assert err != nil
}
