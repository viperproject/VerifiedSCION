package addr

import (
	// @ . "github.com/scionproto/scion/verification/utils/definitions"
	// @ sl "github.com/scionproto/scion/verification/utils/slices"
	"fmt"
	"github.com/scionproto/scion/assertion"
)

func TestIAString_0_0(ia_IA_String IA) {
	var tmp_ia_IA_String IA
	tmp_ia_IA_String = 0x0
	// @ assume ia_IA_String == tmp_ia_IA_String
	res0 := ia_IA_String.String()
	// @ assert "0-0" == res0
}
func TestIAString_1_1(ia_IA_String IA) {
	var tmp_ia_IA_String IA
	tmp_ia_IA_String = 0x1000000000001
	// @ assume ia_IA_String == tmp_ia_IA_String
	res0 := ia_IA_String.String()
	// @ assert "1-1" == res0
}
func TestIAString_65535_1(ia_IA_String IA) {
	var tmp_ia_IA_String IA
	tmp_ia_IA_String = 0xffff000000000001
	// @ assume ia_IA_String == tmp_ia_IA_String
	res0 := ia_IA_String.String()
	// @ assert "65535-1" == res0
}
func TestIAString_1_4294967295(ia_IA_String IA) {
	var tmp_ia_IA_String IA
	tmp_ia_IA_String = 0x10000ffffffff
	// @ assume ia_IA_String == tmp_ia_IA_String
	res0 := ia_IA_String.String()
	// @ assert "1-4294967295" == res0
}
func TestIAString_1_1_0_0(ia_IA_String IA) {
	var tmp_ia_IA_String IA
	tmp_ia_IA_String = 0x1000100000000
	// @ assume ia_IA_String == tmp_ia_IA_String
	res0 := ia_IA_String.String()
	// @ assert "1-1:0:0" == res0
}
func TestIAString_65535_ffff_ffff_ffff(ia_IA_String IA) {
	var tmp_ia_IA_String IA
	tmp_ia_IA_String = 0xffffffffffffffff
	// @ assume ia_IA_String == tmp_ia_IA_String
	res0 := ia_IA_String.String()
	// @ assert "65535-ffff:ffff:ffff" == res0
}
