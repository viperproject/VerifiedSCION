package path

import (
	// @ . "github.com/scionproto/scion/verification/utils/definitions"
	// @ sl "github.com/scionproto/scion/verification/utils/slices"
	"fmt"
	"github.com/scionproto/scion/assertion"
)

func TestHopSerializeDecode(h_HopField_SerializeTo *HopField, b_HopField_SerializeTo []byte, h_HopField_DecodeFromBytes *HopField, raw_HopField_DecodeFromBytes []byte) {
	var tmp_h_HopField_SerializeTo *HopField
	var tmp_b_HopField_SerializeTo []byte
	var tmp_h_HopField_DecodeFromBytes *HopField
	var tmp_raw_HopField_DecodeFromBytes []byte
	tmp_h_HopField_SerializeTo = &HopField{IngressRouterAlert: true, EgressRouterAlert: true, ExpTime: 0x3f, ConsIngress: 0x1, ConsEgress: 0x0, Mac: [6]byte{0x1, 0x2, 0x3, 0x4, 0x5, 0x6}}
	tmp_b_HopField_SerializeTo = []byte{0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}
	tmp_h_HopField_DecodeFromBytes = &HopField{IngressRouterAlert: false, EgressRouterAlert: false, ExpTime: 0x0, ConsIngress: 0x0, ConsEgress: 0x0, Mac: [6]byte{0x0, 0x0, 0x0, 0x0, 0x0, 0x0}}
	tmp_raw_HopField_DecodeFromBytes = []byte{0x3, 0x3f, 0x0, 0x1, 0x0, 0x0, 0x1, 0x2, 0x3, 0x4, 0x5, 0x6}
	// @ inhale  len(b_HopField_SerializeTo) >= HopLen
	// @ inhale acc(h_HopField_SerializeTo.Mem(), R10)
	// @ inhale sl.Bytes(b_HopField_SerializeTo, 0, HopLen)
	// @ exhale acc(tmp_h_HopField_SerializeTo)
	// @ assume h_HopField_SerializeTo == tmp_h_HopField_SerializeTo
	// @ assume b_HopField_SerializeTo === tmp_b_HopField_SerializeTo
	// @ refute false
	err := h_HopField_SerializeTo.SerializeTo(b_HopField_SerializeTo)
	// @ assert unfolding acc(h_HopField_SerializeTo.Mem(), R10) in err == nil

	// @ inhale  acc(h_HopField_DecodeFromBytes)
	// @ inhale  len(raw_HopField_DecodeFromBytes) >= HopLen
	// @ inhale acc(sl.Bytes(raw_HopField_DecodeFromBytes, 0, HopLen), R45)
	// @ exhale acc(tmp_h_HopField_DecodeFromBytes)
	// @ assume h_HopField_DecodeFromBytes == tmp_h_HopField_DecodeFromBytes
	// @ assume raw_HopField_DecodeFromBytes === tmp_raw_HopField_DecodeFromBytes
	// @ refute false
	err := h_HopField_DecodeFromBytes.DecodeFromBytes(b_HopField_SerializeTo)
	// @ assert unfolding h_HopField_DecodeFromBytes.Mem() in err == nil
	// @ assert unfolding h_HopField_DecodeFromBytes.Mem() in HopField{IngressRouterAlert:true, EgressRouterAlert:true, ExpTime:0x3f, ConsIngress:0x1, ConsEgress:0x0, Mac:[6]byte{0x1, 0x2, 0x3, 0x4, 0x5, 0x6}} == *h_HopField_DecodeFromBytes
}
