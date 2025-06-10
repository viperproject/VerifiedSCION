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
	tmp_h_HopField_SerializeTo = &HopField{IngressRouterAlert: true, EgressRouterAlert: true, ExpTime: 63, ConsIngress: 1, ConsEgress: 0, Mac: [6]byte{0x1, 0x2, 0x3, 0x4, 0x5, 0x6}}
	tmp_b_HopField_SerializeTo = []uint8{0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}
	tmp_h_HopField_DecodeFromBytes = &HopField{IngressRouterAlert: false, EgressRouterAlert: false, ExpTime: 0, ConsIngress: 0, ConsEgress: 0, Mac: [6]byte{0x0, 0x0, 0x0, 0x0, 0x0, 0x0}}
	tmp_raw_HopField_DecodeFromBytes = []uint8{0x3, 0x3f, 0x0, 0x1, 0x0, 0x0, 0x1, 0x2, 0x3, 0x4, 0x5, 0x6}
	// @ inhale  len(b_HopField_SerializeTo) >= HopLen
	// @ inhale acc(h_HopField_SerializeTo.Mem(), R10)
	// @ inhale sl.Bytes(b_HopField_SerializeTo, 0, HopLen)
	// @ exhale acc(tmp_h_HopField_SerializeTo)
	// @ assume h_HopField_SerializeTo == tmp_h_HopField_SerializeTo
	// @ assume b_HopField_SerializeTo === tmp_b_HopField_SerializeTo
	// @ refute false
	err := h_HopField_SerializeTo.SerializeTo(b_HopField_SerializeTo)
	// @ unfold acc(h_HopField_SerializeTo.Mem(), R10)
	// @ unfold sl.Bytes(b_HopField_SerializeTo, 0, HopLen)
	// @ ass0_HopField_SerializeTo := err == nil
	// @ assert ass0_HopField_SerializeTo
	// @ fold acc(h_HopField_SerializeTo.Mem(), R10)
	// @ fold sl.Bytes(b_HopField_SerializeTo, 0, HopLen)

	// @ inhale  acc(h_HopField_DecodeFromBytes)
	// @ inhale  len(raw_HopField_DecodeFromBytes) >= HopLen
	// @ inhale acc(sl.Bytes(raw_HopField_DecodeFromBytes, 0, HopLen), R45)
	// @ exhale acc(tmp_h_HopField_DecodeFromBytes)
	// @ assume h_HopField_DecodeFromBytes == tmp_h_HopField_DecodeFromBytes
	// @ assume raw_HopField_DecodeFromBytes === tmp_raw_HopField_DecodeFromBytes
	// @ refute false
	err := h_HopField_DecodeFromBytes.DecodeFromBytes(b_HopField_SerializeTo)
	// @ unfold acc(sl.Bytes(b_HopField_SerializeTo, 0, HopLen), R45)
	// @ unfold   h_HopField_DecodeFromBytes.Mem()
	// @ ass0_HopField_DecodeFromBytes := err == nil
	// @ assert ass0_HopField_DecodeFromBytes
	// @ ass1_HopField_DecodeFromBytes := HopField{IngressRouterAlert:true, EgressRouterAlert:true, ExpTime:0x3f, ConsIngress:0x1, ConsEgress:0x0, Mac:[6]byte{0x1, 0x2, 0x3, 0x4, 0x5, 0x6}} == *h_HopField_DecodeFromBytes
	// @ assert ass1_HopField_DecodeFromBytes
	// @ fold acc(sl.Bytes(b_HopField_SerializeTo, 0, HopLen), R45)
	// @ fold   h_HopField_DecodeFromBytes.Mem()
}
