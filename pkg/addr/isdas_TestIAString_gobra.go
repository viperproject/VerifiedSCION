package addr

import (
	// @ . "github.com/scionproto/scion/verification/utils/definitions"
	// @ sl "github.com/scionproto/scion/verification/utils/slices"
	"fmt"
	"github.com/scionproto/scion/assertion"
)

func TestIAString_0_0(ia_IA_String IA) {
	var tmp_ia_IA_String IA
	tmp_ia_IA_String = 0
	// @ assume ia_IA_String == tmp_ia_IA_String
	res0 := ia_IA_String.String()
	// @ ass0_IA_String := "0-0" == res0
	// @ assert ass0_IA_String
}
func TestIAString_1_1(ia_IA_String IA) {
	var tmp_ia_IA_String IA
	tmp_ia_IA_String = 281474976710657
	// @ assume ia_IA_String == tmp_ia_IA_String
	res0 := ia_IA_String.String()
	// @ ass0_IA_String := "1-1" == res0
	// @ assert ass0_IA_String
}
func TestIAString_65535_1(ia_IA_String IA) {
	var tmp_ia_IA_String IA
	tmp_ia_IA_String = 18446462598732840961
	// @ assume ia_IA_String == tmp_ia_IA_String
	res0 := ia_IA_String.String()
	// @ ass0_IA_String := "65535-1" == res0
	// @ assert ass0_IA_String
}
func TestIAString_1_4294967295(ia_IA_String IA) {
	var tmp_ia_IA_String IA
	tmp_ia_IA_String = 281479271677951
	// @ assume ia_IA_String == tmp_ia_IA_String
	res0 := ia_IA_String.String()
	// @ ass0_IA_String := "1-4294967295" == res0
	// @ assert ass0_IA_String
}
func TestIAString_1_1_0_0(ia_IA_String IA) {
	var tmp_ia_IA_String IA
	tmp_ia_IA_String = 281479271677952
	// @ assume ia_IA_String == tmp_ia_IA_String
	res0 := ia_IA_String.String()
	// @ ass0_IA_String := "1-1:0:0" == res0
	// @ assert ass0_IA_String
}
func TestIAString_65535_ffff_ffff_ffff(ia_IA_String IA) {
	var tmp_ia_IA_String IA
	tmp_ia_IA_String = 18446744073709551615
	// @ assume ia_IA_String == tmp_ia_IA_String
	res0 := ia_IA_String.String()
	// @ ass0_IA_String := "65535-ffff:ffff:ffff" == res0
	// @ assert ass0_IA_String
}
