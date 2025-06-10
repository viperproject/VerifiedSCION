package addr

import (
	// @ . "github.com/scionproto/scion/verification/utils/definitions"
	// @ sl "github.com/scionproto/scion/verification/utils/slices"
	"fmt"
	"github.com/scionproto/scion/assertion"
)

func TestASString_0(_as_AS_String AS) {
	var tmp__as_AS_String AS
	tmp__as_AS_String = 0
	// @ inhale _as_AS_String.inRange()
	// @ assume _as_AS_String == tmp__as_AS_String
	res0 := _as_AS_String.String()
	// @ ass0_AS_String := "0" == res0
	// @ assert ass0_AS_String
}
func TestASString_1(_as_AS_String AS) {
	var tmp__as_AS_String AS
	tmp__as_AS_String = 1
	// @ inhale _as_AS_String.inRange()
	// @ assume _as_AS_String == tmp__as_AS_String
	res0 := _as_AS_String.String()
	// @ ass0_AS_String := "1" == res0
	// @ assert ass0_AS_String
}
func TestASString_999(_as_AS_String AS) {
	var tmp__as_AS_String AS
	tmp__as_AS_String = 999
	// @ inhale _as_AS_String.inRange()
	// @ assume _as_AS_String == tmp__as_AS_String
	res0 := _as_AS_String.String()
	// @ ass0_AS_String := "999" == res0
	// @ assert ass0_AS_String
}
func TestASString_4294967295(_as_AS_String AS) {
	var tmp__as_AS_String AS
	tmp__as_AS_String = 4294967295
	// @ inhale _as_AS_String.inRange()
	// @ assume _as_AS_String == tmp__as_AS_String
	res0 := _as_AS_String.String()
	// @ ass0_AS_String := "4294967295" == res0
	// @ assert ass0_AS_String
}
func TestASString_1_0_0(_as_AS_String AS) {
	var tmp__as_AS_String AS
	tmp__as_AS_String = 4294967296
	// @ inhale _as_AS_String.inRange()
	// @ assume _as_AS_String == tmp__as_AS_String
	res0 := _as_AS_String.String()
	// @ ass0_AS_String := "1:0:0" == res0
	// @ assert ass0_AS_String
}
func TestASString_1_fcd1_1(_as_AS_String AS) {
	var tmp__as_AS_String AS
	tmp__as_AS_String = 8536522753
	// @ inhale _as_AS_String.inRange()
	// @ assume _as_AS_String == tmp__as_AS_String
	res0 := _as_AS_String.String()
	// @ ass0_AS_String := "1:fcd1:1" == res0
	// @ assert ass0_AS_String
}
func TestASString_ffff_ffff_ffff(_as_AS_String AS) {
	var tmp__as_AS_String AS
	tmp__as_AS_String = 281474976710655
	// @ inhale _as_AS_String.inRange()
	// @ assume _as_AS_String == tmp__as_AS_String
	res0 := _as_AS_String.String()
	// @ ass0_AS_String := "ffff:ffff:ffff" == res0
	// @ assert ass0_AS_String
}
func TestASString_281474976710656__Illegal_AS__larger_than_281474976710655_(_as_AS_String AS) {
	var tmp__as_AS_String AS
	tmp__as_AS_String = 281474976710656
	// @ inhale _as_AS_String.inRange()
	// @ assume _as_AS_String == tmp__as_AS_String
	res0 := _as_AS_String.String()
	// @ ass0_AS_String := "281474976710656 [Illegal AS: larger than 281474976710655]" == res0
	// @ assert ass0_AS_String
}
