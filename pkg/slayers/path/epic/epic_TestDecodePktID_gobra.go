package epic

import (
	// @ . "github.com/scionproto/scion/verification/utils/definitions"
	// @ sl "github.com/scionproto/scion/verification/utils/slices"
	"fmt"
	"github.com/scionproto/scion/assertion"
)

func TestDecodePktID_Max__timestamp(i_PktID_DecodeFromBytes *PktID, raw_PktID_DecodeFromBytes []byte) {
	var tmp_i_PktID_DecodeFromBytes *PktID
	var tmp_raw_PktID_DecodeFromBytes []byte
	tmp_i_PktID_DecodeFromBytes = &PktID{Timestamp: 0, Counter: 0}
	tmp_raw_PktID_DecodeFromBytes = []uint8{0xff, 0xff, 0xff, 0xff, 0x2, 0x0, 0x0, 0x3}
	// @ inhale  len(raw_PktID_DecodeFromBytes) >= PktIDLen
	// @ inhale acc(i_PktID_DecodeFromBytes)
	// @ inhale acc(sl.Bytes(raw_PktID_DecodeFromBytes, 0, len(raw_PktID_DecodeFromBytes)), R42)
	// @ exhale acc(tmp_i_PktID_DecodeFromBytes)
	// @ assume i_PktID_DecodeFromBytes == tmp_i_PktID_DecodeFromBytes
	// @ assume raw_PktID_DecodeFromBytes === tmp_raw_PktID_DecodeFromBytes
	i_PktID_DecodeFromBytes.DecodeFromBytes(raw_PktID_DecodeFromBytes)
	// @ ass0_PktID_DecodeFromBytes := PktID{Timestamp:0xffffffff, Counter:0x2000003} == *i_PktID_DecodeFromBytes
	// @ assert ass0_PktID_DecodeFromBytes
}
func TestDecodePktID_Basic(i_PktID_DecodeFromBytes *PktID, raw_PktID_DecodeFromBytes []byte) {
	var tmp_i_PktID_DecodeFromBytes *PktID
	var tmp_raw_PktID_DecodeFromBytes []byte
	tmp_i_PktID_DecodeFromBytes = &PktID{Timestamp: 0, Counter: 0}
	tmp_raw_PktID_DecodeFromBytes = []uint8{0x0, 0x0, 0x0, 0x1, 0x2, 0x0, 0x0, 0x3}
	// @ inhale  len(raw_PktID_DecodeFromBytes) >= PktIDLen
	// @ inhale acc(i_PktID_DecodeFromBytes)
	// @ inhale acc(sl.Bytes(raw_PktID_DecodeFromBytes, 0, len(raw_PktID_DecodeFromBytes)), R42)
	// @ exhale acc(tmp_i_PktID_DecodeFromBytes)
	// @ assume i_PktID_DecodeFromBytes == tmp_i_PktID_DecodeFromBytes
	// @ assume raw_PktID_DecodeFromBytes === tmp_raw_PktID_DecodeFromBytes
	i_PktID_DecodeFromBytes.DecodeFromBytes(raw_PktID_DecodeFromBytes)
	// @ ass0_PktID_DecodeFromBytes := PktID{Timestamp:0x1, Counter:0x2000003} == *i_PktID_DecodeFromBytes
	// @ assert ass0_PktID_DecodeFromBytes
}
