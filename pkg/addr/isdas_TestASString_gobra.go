package addr

import (
	// @ . "github.com/scionproto/scion/verification/utils/definitions"
	// @ sl "github.com/scionproto/scion/verification/utils/slices"
	"fmt"
	"github.com/scionproto/scion/assertion"
)

func TestASString_0(_as_AS_String AS) {
	var tmp__as_AS_String AS
	tmp__as_AS_String = 0x0
	// @ inhale _as_AS_String.inRange()
	// @ assume _as_AS_String == tmp__as_AS_String
	res0 := _as_AS_String.String()
	// @ assert "0" == res0
}
func TestASString_1(_as_AS_String AS) {
	var tmp__as_AS_String AS
	tmp__as_AS_String = 0x1
	// @ inhale _as_AS_String.inRange()
	// @ assume _as_AS_String == tmp__as_AS_String
	res0 := _as_AS_String.String()
	// @ assert "1" == res0
}
func TestASString_999(_as_AS_String AS) {
	var tmp__as_AS_String AS
	tmp__as_AS_String = 0x3e7
	// @ inhale _as_AS_String.inRange()
	// @ assume _as_AS_String == tmp__as_AS_String
	res0 := _as_AS_String.String()
	// @ assert "999" == res0
}
func TestASString_4294967295(_as_AS_String AS) {
	var tmp__as_AS_String AS
	tmp__as_AS_String = 0xffffffff
	// @ inhale _as_AS_String.inRange()
	// @ assume _as_AS_String == tmp__as_AS_String
	res0 := _as_AS_String.String()
	// @ assert "4294967295" == res0
}
func TestASString_1_0_0(_as_AS_String AS) {
	var tmp__as_AS_String AS
	tmp__as_AS_String = 0x100000000
	// @ inhale _as_AS_String.inRange()
	// @ assume _as_AS_String == tmp__as_AS_String
	res0 := _as_AS_String.String()
	// @ assert "1:0:0" == res0
}
func TestASString_1_fcd1_1(_as_AS_String AS) {
	var tmp__as_AS_String AS
	tmp__as_AS_String = 0x1fcd10001
	// @ inhale _as_AS_String.inRange()
	// @ assume _as_AS_String == tmp__as_AS_String
	res0 := _as_AS_String.String()
	// @ assert "1:fcd1:1" == res0
}
func TestASString_ffff_ffff_ffff(_as_AS_String AS) {
	var tmp__as_AS_String AS
	tmp__as_AS_String = 0xffffffffffff
	// @ inhale _as_AS_String.inRange()
	// @ assume _as_AS_String == tmp__as_AS_String
	res0 := _as_AS_String.String()
	// @ assert "ffff:ffff:ffff" == res0
}
func TestASString_281474976710656__Illegal_AS__larger_than_281474976710655_(_as_AS_String AS) {
	var tmp__as_AS_String AS
	tmp__as_AS_String = 0x1000000000000
	// @ inhale _as_AS_String.inRange()
	// @ assume _as_AS_String == tmp__as_AS_String
	res0 := _as_AS_String.String()
	// @ assert "281474976710656 [Illegal AS: larger than 281474976710655]" == res0
}
