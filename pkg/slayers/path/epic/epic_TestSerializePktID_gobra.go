package epic

import (
	// @ . "github.com/scionproto/scion/verification/utils/definitions"
	// @ sl "github.com/scionproto/scion/verification/utils/slices"
	"fmt"
	"github.com/scionproto/scion/assertion"
)

func TestSerializePktID_Max__timestamp(i_PktID_SerializeTo *PktID, b_PktID_SerializeTo []byte) {
	var tmp_i_PktID_SerializeTo *PktID
	var tmp_b_PktID_SerializeTo []byte
	tmp_i_PktID_SerializeTo = &PktID{Timestamp: 4294967295, Counter: 33554435}
	tmp_b_PktID_SerializeTo = []uint8{0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}
	// @ inhale  len(b_PktID_SerializeTo) >= PktIDLen
	// @ inhale acc(i_PktID_SerializeTo, R1)
	// @ inhale sl.Bytes(b_PktID_SerializeTo, 0, len(b_PktID_SerializeTo))
	// @ exhale acc(tmp_i_PktID_SerializeTo)
	// @ assume i_PktID_SerializeTo == tmp_i_PktID_SerializeTo
	// @ assume b_PktID_SerializeTo === tmp_b_PktID_SerializeTo
	i_PktID_SerializeTo.SerializeTo(b_PktID_SerializeTo)
	// @ ass0_PktID_SerializeTo := assertion.EqualSliceByte([]byte{0xff, 0xff, 0xff, 0xff, 0x2, 0x0, 0x0, 0x3} ,  b_PktID_SerializeTo)
	// @ assert ass0_PktID_SerializeTo
}
func TestSerializePktID_Basic(i_PktID_SerializeTo *PktID, b_PktID_SerializeTo []byte) {
	var tmp_i_PktID_SerializeTo *PktID
	var tmp_b_PktID_SerializeTo []byte
	tmp_i_PktID_SerializeTo = &PktID{Timestamp: 1, Counter: 33554435}
	tmp_b_PktID_SerializeTo = []uint8{0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}
	// @ inhale  len(b_PktID_SerializeTo) >= PktIDLen
	// @ inhale acc(i_PktID_SerializeTo, R1)
	// @ inhale sl.Bytes(b_PktID_SerializeTo, 0, len(b_PktID_SerializeTo))
	// @ exhale acc(tmp_i_PktID_SerializeTo)
	// @ assume i_PktID_SerializeTo == tmp_i_PktID_SerializeTo
	// @ assume b_PktID_SerializeTo === tmp_b_PktID_SerializeTo
	i_PktID_SerializeTo.SerializeTo(b_PktID_SerializeTo)
	// @ ass0_PktID_SerializeTo := assertion.EqualSliceByte([]byte{0x0, 0x0, 0x0, 0x1, 0x2, 0x0, 0x0, 0x3} ,  b_PktID_SerializeTo)
	// @ assert ass0_PktID_SerializeTo
}
