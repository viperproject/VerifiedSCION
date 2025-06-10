package addr

import (
	// @ . "github.com/scionproto/scion/verification/utils/definitions"
	// @ sl "github.com/scionproto/scion/verification/utils/slices"
	"fmt"
	"github.com/scionproto/scion/assertion"
)

func TestParseISD__00(s_ParseISD string) {
	var tmp_s_ParseISD string
	tmp_s_ParseISD = ""
	// @ assume s_ParseISD == tmp_s_ParseISD
	res0, err := ParseISD(s_ParseISD)
	// @ assert err != nil
}
func TestParseISD_a(s_ParseISD string) {
	var tmp_s_ParseISD string
	tmp_s_ParseISD = "a"
	// @ assume s_ParseISD == tmp_s_ParseISD
	res0, err := ParseISD(s_ParseISD)
	// @ assert err != nil
}
func TestParseISD_0(s_ParseISD string) {
	var tmp_s_ParseISD string
	tmp_s_ParseISD = "0"
	// @ assume s_ParseISD == tmp_s_ParseISD
	// @ refute false
	res0, err := ParseISD(s_ParseISD)
	// @ assert err == nil
	// @ assert err == nil
	// @ assert 0x0 == res0
}
func TestParseISD_1(s_ParseISD string) {
	var tmp_s_ParseISD string
	tmp_s_ParseISD = "1"
	// @ assume s_ParseISD == tmp_s_ParseISD
	// @ refute false
	res0, err := ParseISD(s_ParseISD)
	// @ assert err == nil
	// @ assert err == nil
	// @ assert 0x1 == res0
}
func TestParseISD_65535(s_ParseISD string) {
	var tmp_s_ParseISD string
	tmp_s_ParseISD = "65535"
	// @ assume s_ParseISD == tmp_s_ParseISD
	// @ refute false
	res0, err := ParseISD(s_ParseISD)
	// @ assert err == nil
	// @ assert err == nil
	// @ assert 0xffff == res0
}
func TestParseISD_65536(s_ParseISD string) {
	var tmp_s_ParseISD string
	tmp_s_ParseISD = "65536"
	// @ assume s_ParseISD == tmp_s_ParseISD
	res0, err := ParseISD(s_ParseISD)
	// @ assert err != nil
}
