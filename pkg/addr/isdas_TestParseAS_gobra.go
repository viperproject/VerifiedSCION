package addr

import (
	// @ . "github.com/scionproto/scion/verification/utils/definitions"
	// @ sl "github.com/scionproto/scion/verification/utils/slices"
	"fmt"
	"github.com/scionproto/scion/assertion"
)

func TestParseAS__00(_as_ParseAS string) {
	var tmp__as_ParseAS string
	tmp__as_ParseAS = ""
	// @ assume _as_ParseAS == tmp__as_ParseAS
	retAs, err := ParseAS(_as_ParseAS)
	// @ ass0_ParseAS := err != nil
	// @ assert ass0_ParseAS
}
func TestParseAS_0(_as_ParseAS string) {
	var tmp__as_ParseAS string
	tmp__as_ParseAS = "0"
	// @ assume _as_ParseAS == tmp__as_ParseAS
	// @ refute false
	retAs, err := ParseAS(_as_ParseAS)
	// @ ass0_ParseAS := err == nil
	// @ assert ass0_ParseAS
	// @ ass1_ParseAS := err == nil
	// @ assert ass1_ParseAS
	// @ ass2_ParseAS := 0x0 == retAs
	// @ assert ass2_ParseAS
}
func TestParseAS_0x0(_as_ParseAS string) {
	var tmp__as_ParseAS string
	tmp__as_ParseAS = "0x0"
	// @ assume _as_ParseAS == tmp__as_ParseAS
	retAs, err := ParseAS(_as_ParseAS)
	// @ ass0_ParseAS := err != nil
	// @ assert ass0_ParseAS
}
func TestParseAS_ff(_as_ParseAS string) {
	var tmp__as_ParseAS string
	tmp__as_ParseAS = "ff"
	// @ assume _as_ParseAS == tmp__as_ParseAS
	retAs, err := ParseAS(_as_ParseAS)
	// @ ass0_ParseAS := err != nil
	// @ assert ass0_ParseAS
}
func TestParseAS_1(_as_ParseAS string) {
	var tmp__as_ParseAS string
	tmp__as_ParseAS = "1"
	// @ assume _as_ParseAS == tmp__as_ParseAS
	// @ refute false
	retAs, err := ParseAS(_as_ParseAS)
	// @ ass0_ParseAS := err == nil
	// @ assert ass0_ParseAS
	// @ ass1_ParseAS := err == nil
	// @ assert ass1_ParseAS
	// @ ass2_ParseAS := 0x1 == retAs
	// @ assert ass2_ParseAS
}
func TestParseAS_4294967295(_as_ParseAS string) {
	var tmp__as_ParseAS string
	tmp__as_ParseAS = "4294967295"
	// @ assume _as_ParseAS == tmp__as_ParseAS
	// @ refute false
	retAs, err := ParseAS(_as_ParseAS)
	// @ ass0_ParseAS := err == nil
	// @ assert ass0_ParseAS
	// @ ass1_ParseAS := err == nil
	// @ assert ass1_ParseAS
	// @ ass2_ParseAS := 0xffffffff == retAs
	// @ assert ass2_ParseAS
}
func TestParseAS_4294967296(_as_ParseAS string) {
	var tmp__as_ParseAS string
	tmp__as_ParseAS = "4294967296"
	// @ assume _as_ParseAS == tmp__as_ParseAS
	retAs, err := ParseAS(_as_ParseAS)
	// @ ass0_ParseAS := err != nil
	// @ assert ass0_ParseAS
}
func TestParseAS__(_as_ParseAS string) {
	var tmp__as_ParseAS string
	tmp__as_ParseAS = ":"
	// @ assume _as_ParseAS == tmp__as_ParseAS
	retAs, err := ParseAS(_as_ParseAS)
	// @ ass0_ParseAS := err != nil
	// @ assert ass0_ParseAS
}
func TestParseAS_0_0_0(_as_ParseAS string) {
	var tmp__as_ParseAS string
	tmp__as_ParseAS = "0:0:0"
	// @ assume _as_ParseAS == tmp__as_ParseAS
	// @ refute false
	retAs, err := ParseAS(_as_ParseAS)
	// @ ass0_ParseAS := err == nil
	// @ assert ass0_ParseAS
	// @ ass1_ParseAS := err == nil
	// @ assert ass1_ParseAS
	// @ ass2_ParseAS := 0x0 == retAs
	// @ assert ass2_ParseAS
}
func TestParseAS_0_0_0_(_as_ParseAS string) {
	var tmp__as_ParseAS string
	tmp__as_ParseAS = "0:0:0:"
	// @ assume _as_ParseAS == tmp__as_ParseAS
	retAs, err := ParseAS(_as_ParseAS)
	// @ ass0_ParseAS := err != nil
	// @ assert ass0_ParseAS
}
func TestParseAS__0_0_(_as_ParseAS string) {
	var tmp__as_ParseAS string
	tmp__as_ParseAS = ":0:0:"
	// @ assume _as_ParseAS == tmp__as_ParseAS
	retAs, err := ParseAS(_as_ParseAS)
	// @ ass0_ParseAS := err != nil
	// @ assert ass0_ParseAS
}
func TestParseAS_0_0(_as_ParseAS string) {
	var tmp__as_ParseAS string
	tmp__as_ParseAS = "0:0"
	// @ assume _as_ParseAS == tmp__as_ParseAS
	retAs, err := ParseAS(_as_ParseAS)
	// @ ass0_ParseAS := err != nil
	// @ assert ass0_ParseAS
}
func TestParseAS_0_0_1(_as_ParseAS string) {
	var tmp__as_ParseAS string
	tmp__as_ParseAS = "0:0:1"
	// @ assume _as_ParseAS == tmp__as_ParseAS
	// @ refute false
	retAs, err := ParseAS(_as_ParseAS)
	// @ ass0_ParseAS := err == nil
	// @ assert ass0_ParseAS
	// @ ass1_ParseAS := err == nil
	// @ assert ass1_ParseAS
	// @ ass2_ParseAS := 0x1 == retAs
	// @ assert ass2_ParseAS
}
func TestParseAS_1_0_0(_as_ParseAS string) {
	var tmp__as_ParseAS string
	tmp__as_ParseAS = "1:0:0"
	// @ assume _as_ParseAS == tmp__as_ParseAS
	// @ refute false
	retAs, err := ParseAS(_as_ParseAS)
	// @ ass0_ParseAS := err == nil
	// @ assert ass0_ParseAS
	// @ ass1_ParseAS := err == nil
	// @ assert ass1_ParseAS
	// @ ass2_ParseAS := 0x100000000 == retAs
	// @ assert ass2_ParseAS
}
func TestParseAS_ffff_ffff_ffff(_as_ParseAS string) {
	var tmp__as_ParseAS string
	tmp__as_ParseAS = "ffff:ffff:ffff"
	// @ assume _as_ParseAS == tmp__as_ParseAS
	// @ refute false
	retAs, err := ParseAS(_as_ParseAS)
	// @ ass0_ParseAS := err == nil
	// @ assert ass0_ParseAS
	// @ ass1_ParseAS := err == nil
	// @ assert ass1_ParseAS
	// @ ass2_ParseAS := 0xffffffffffff == retAs
	// @ assert ass2_ParseAS
}
func TestParseAS_10000_0_0(_as_ParseAS string) {
	var tmp__as_ParseAS string
	tmp__as_ParseAS = "10000:0:0"
	// @ assume _as_ParseAS == tmp__as_ParseAS
	retAs, err := ParseAS(_as_ParseAS)
	// @ ass0_ParseAS := err != nil
	// @ assert ass0_ParseAS
}
func TestParseAS_0_10000_0(_as_ParseAS string) {
	var tmp__as_ParseAS string
	tmp__as_ParseAS = "0:10000:0"
	// @ assume _as_ParseAS == tmp__as_ParseAS
	retAs, err := ParseAS(_as_ParseAS)
	// @ ass0_ParseAS := err != nil
	// @ assert ass0_ParseAS
}
func TestParseAS_0_0_10000(_as_ParseAS string) {
	var tmp__as_ParseAS string
	tmp__as_ParseAS = "0:0:10000"
	// @ assume _as_ParseAS == tmp__as_ParseAS
	retAs, err := ParseAS(_as_ParseAS)
	// @ ass0_ParseAS := err != nil
	// @ assert ass0_ParseAS
}
func TestParseAS_0_0x0_0(_as_ParseAS string) {
	var tmp__as_ParseAS string
	tmp__as_ParseAS = "0:0x0:0"
	// @ assume _as_ParseAS == tmp__as_ParseAS
	retAs, err := ParseAS(_as_ParseAS)
	// @ ass0_ParseAS := err != nil
	// @ assert ass0_ParseAS
}
