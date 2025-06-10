package path

import (
	// @ . "github.com/scionproto/scion/verification/utils/definitions"
	// @ sl "github.com/scionproto/scion/verification/utils/slices"
	"fmt"
	"github.com/scionproto/scion/assertion"
)

func TestInfoSerializeDecode(inf_InfoField_SerializeTo *InfoField, b_InfoField_SerializeTo []byte, inf_InfoField_DecodeFromBytes *InfoField, raw_InfoField_DecodeFromBytes []byte) {
	var tmp_inf_InfoField_SerializeTo *InfoField
	var tmp_b_InfoField_SerializeTo []byte
	var tmp_inf_InfoField_DecodeFromBytes *InfoField
	var tmp_raw_InfoField_DecodeFromBytes []byte
	tmp_inf_InfoField_SerializeTo = &InfoField{Peer: true, ConsDir: true, SegID: 0x222, Timestamp: 0x100}
	tmp_b_InfoField_SerializeTo = []byte{0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}
	tmp_inf_InfoField_DecodeFromBytes = &InfoField{Peer: false, ConsDir: false, SegID: 0x0, Timestamp: 0x0}
	tmp_raw_InfoField_DecodeFromBytes = []byte{0x3, 0x0, 0x2, 0x22, 0x0, 0x0, 0x1, 0x0}
	// @ inhale  len(b_InfoField_SerializeTo) >= InfoLen
	// @ inhale acc(inf_InfoField_SerializeTo, R10)
	// @ inhale sl.Bytes(b_InfoField_SerializeTo, 0, len(b_InfoField_SerializeTo))
	// @ exhale acc(tmp_inf_InfoField_SerializeTo)
	// @ assume inf_InfoField_SerializeTo == tmp_inf_InfoField_SerializeTo
	// @ assume b_InfoField_SerializeTo === tmp_b_InfoField_SerializeTo
	// @ refute false
	err := inf_InfoField_SerializeTo.SerializeTo(b_InfoField_SerializeTo)
	// @ assert unfolding sl.Bytes(b_InfoField_SerializeTo, 0, len(b_InfoField_SerializeTo)) in err == nil

	// @ inhale  len(raw_InfoField_DecodeFromBytes) >= InfoLen
	// @ inhale acc(inf_InfoField_DecodeFromBytes)
	// @ inhale acc(sl.Bytes(raw_InfoField_DecodeFromBytes, 0, len(raw_InfoField_DecodeFromBytes)), R45)
	// @ exhale acc(tmp_inf_InfoField_DecodeFromBytes)
	// @ assume inf_InfoField_DecodeFromBytes == tmp_inf_InfoField_DecodeFromBytes
	// @ assume raw_InfoField_DecodeFromBytes === tmp_raw_InfoField_DecodeFromBytes
	// @ refute false
	err := inf_InfoField_DecodeFromBytes.DecodeFromBytes(b_InfoField_SerializeTo)
	// @ assert err == nil
	// @ assert unfolding acc(sl.Bytes(b_InfoField_SerializeTo, 0, len(b_InfoField_SerializeTo)), R45) in InfoField{Peer:true, ConsDir:true, SegID:0x222, Timestamp:0x100} == *inf_InfoField_DecodeFromBytes
}
