package addr

import (
	// @ . "github.com/scionproto/scion/verification/utils/definitions"
	// @ sl "github.com/scionproto/scion/verification/utils/slices"
	"fmt"
	"github.com/scionproto/scion/assertion"
)

func TestParseIA__00(ia_ParseIA string) {
	var tmp_ia_ParseIA string
	tmp_ia_ParseIA = ""
	// @ assume ia_ParseIA == tmp_ia_ParseIA
	res0, err := ParseIA(ia_ParseIA)
	// @ assert err != nil
}
func TestParseIA_a(ia_ParseIA string) {
	var tmp_ia_ParseIA string
	tmp_ia_ParseIA = "a"
	// @ assume ia_ParseIA == tmp_ia_ParseIA
	res0, err := ParseIA(ia_ParseIA)
	// @ assert err != nil
}
func TestParseIA_1a_2b(ia_ParseIA string) {
	var tmp_ia_ParseIA string
	tmp_ia_ParseIA = "1a-2b"
	// @ assume ia_ParseIA == tmp_ia_ParseIA
	res0, err := ParseIA(ia_ParseIA)
	// @ assert err != nil
}
func TestParseIA__(ia_ParseIA string) {
	var tmp_ia_ParseIA string
	tmp_ia_ParseIA = "-"
	// @ assume ia_ParseIA == tmp_ia_ParseIA
	res0, err := ParseIA(ia_ParseIA)
	// @ assert err != nil
}
func TestParseIA_1_(ia_ParseIA string) {
	var tmp_ia_ParseIA string
	tmp_ia_ParseIA = "1-"
	// @ assume ia_ParseIA == tmp_ia_ParseIA
	res0, err := ParseIA(ia_ParseIA)
	// @ assert err != nil
}
func TestParseIA__1(ia_ParseIA string) {
	var tmp_ia_ParseIA string
	tmp_ia_ParseIA = "-1"
	// @ assume ia_ParseIA == tmp_ia_ParseIA
	res0, err := ParseIA(ia_ParseIA)
	// @ assert err != nil
}
func TestParseIA__1_(ia_ParseIA string) {
	var tmp_ia_ParseIA string
	tmp_ia_ParseIA = "-1-"
	// @ assume ia_ParseIA == tmp_ia_ParseIA
	res0, err := ParseIA(ia_ParseIA)
	// @ assert err != nil
}
func TestParseIA_1__1(ia_ParseIA string) {
	var tmp_ia_ParseIA string
	tmp_ia_ParseIA = "1--1"
	// @ assume ia_ParseIA == tmp_ia_ParseIA
	res0, err := ParseIA(ia_ParseIA)
	// @ assert err != nil
}
func TestParseIA_0_0(ia_ParseIA string) {
	var tmp_ia_ParseIA string
	tmp_ia_ParseIA = "0-0"
	// @ assume ia_ParseIA == tmp_ia_ParseIA
	// @ refute false
	res0, err := ParseIA(ia_ParseIA)
	// @ assert err == nil
	// @ assert 0x0 == res0
}
func TestParseIA_1_1(ia_ParseIA string) {
	var tmp_ia_ParseIA string
	tmp_ia_ParseIA = "1-1"
	// @ assume ia_ParseIA == tmp_ia_ParseIA
	// @ refute false
	res0, err := ParseIA(ia_ParseIA)
	// @ assert err == nil
	// @ assert 0x1000000000001 == res0
}
func TestParseIA_65535_1(ia_ParseIA string) {
	var tmp_ia_ParseIA string
	tmp_ia_ParseIA = "65535-1"
	// @ assume ia_ParseIA == tmp_ia_ParseIA
	// @ refute false
	res0, err := ParseIA(ia_ParseIA)
	// @ assert err == nil
	// @ assert 0xffff000000000001 == res0
}
func TestParseIA_65536_1(ia_ParseIA string) {
	var tmp_ia_ParseIA string
	tmp_ia_ParseIA = "65536-1"
	// @ assume ia_ParseIA == tmp_ia_ParseIA
	res0, err := ParseIA(ia_ParseIA)
	// @ assert err != nil
}
func TestParseIA_1_4294967295(ia_ParseIA string) {
	var tmp_ia_ParseIA string
	tmp_ia_ParseIA = "1-4294967295"
	// @ assume ia_ParseIA == tmp_ia_ParseIA
	// @ refute false
	res0, err := ParseIA(ia_ParseIA)
	// @ assert err == nil
	// @ assert 0x10000ffffffff == res0
}
func TestParseIA_1_4294967296(ia_ParseIA string) {
	var tmp_ia_ParseIA string
	tmp_ia_ParseIA = "1-4294967296"
	// @ assume ia_ParseIA == tmp_ia_ParseIA
	res0, err := ParseIA(ia_ParseIA)
	// @ assert err != nil
}
func TestParseIA_1_1_0_0(ia_ParseIA string) {
	var tmp_ia_ParseIA string
	tmp_ia_ParseIA = "1-1:0:0"
	// @ assume ia_ParseIA == tmp_ia_ParseIA
	// @ refute false
	res0, err := ParseIA(ia_ParseIA)
	// @ assert err == nil
	// @ assert 0x1000100000000 == res0
}
func TestParseIA_1_1_fcd1_1(ia_ParseIA string) {
	var tmp_ia_ParseIA string
	tmp_ia_ParseIA = "1-1:fcd1:1"
	// @ assume ia_ParseIA == tmp_ia_ParseIA
	// @ refute false
	res0, err := ParseIA(ia_ParseIA)
	// @ assert err == nil
	// @ assert 0x10001fcd10001 == res0
}
func TestParseIA_1_ffff_ffff_10000(ia_ParseIA string) {
	var tmp_ia_ParseIA string
	tmp_ia_ParseIA = "1-ffff:ffff:10000"
	// @ assume ia_ParseIA == tmp_ia_ParseIA
	res0, err := ParseIA(ia_ParseIA)
	// @ assert err != nil
}
func TestParseIA_65535_ffff_ffff_ffff(ia_ParseIA string) {
	var tmp_ia_ParseIA string
	tmp_ia_ParseIA = "65535-ffff:ffff:ffff"
	// @ assume ia_ParseIA == tmp_ia_ParseIA
	// @ refute false
	res0, err := ParseIA(ia_ParseIA)
	// @ assert err == nil
	// @ assert 0xffffffffffffffff == res0
}
