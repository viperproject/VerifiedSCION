package path

func TestHopSerializeDecode(h_HopField_SerializeTo *HopField, b_HopField_SerializeTo []byte, h_HopField_DecodeFromBytes *HopField, raw_HopField_DecodeFromBytes []byte) {
	var tmp_h_HopField_SerializeTo *HopField
	var tmp_b_HopField_SerializeTo []byte
	var tmp_h_HopField_DecodeFromBytes *HopField
	var tmp_raw_HopField_DecodeFromBytes []byte
	tmp_h_HopField_SerializeTo = &HopField{IngressRouterAlert: true, EgressRouterAlert: true, ExpTime: 0x3f, ConsIngress: 0x1, ConsEgress: 0x0, Mac: [6]uint8{0x1, 0x2, 0x3, 0x4, 0x5, 0x6}}
	tmp_b_HopField_SerializeTo = []byte{0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}
	tmp_h_HopField_DecodeFromBytes = &HopField{IngressRouterAlert: false, EgressRouterAlert: false, ExpTime: 0x0, ConsIngress: 0x0, ConsEgress: 0x0, Mac: [6]uint8{0x0, 0x0, 0x0, 0x0, 0x0, 0x0}}
	tmp_raw_HopField_DecodeFromBytes = []byte{0x3, 0x3f, 0x0, 0x1, 0x0, 0x0, 0x1, 0x2, 0x3, 0x4, 0x5, 0x6}
	// @ inhale  len(b_HopField_SerializeTo) >= HopLen
	// @ inhale acc(h_HopField_SerializeTo.Mem(), R10)
	// @ inhale sl.Bytes(b_HopField_SerializeTo, 0, HopLen)
	// @ assume h_HopField_SerializeTo == tmp_h_HopField_SerializeTo
	// @ assume b_HopField_SerializeTo === tmp_b_HopField_SerializeTo
	// @ assume h_HopField_DecodeFromBytes == tmp_h_HopField_DecodeFromBytes
	// @ assume raw_HopField_DecodeFromBytes === tmp_raw_HopField_DecodeFromBytes
	// @ refute false
	err := tmp_h_HopField_SerializeTo.SerializeTo(tmp_b_HopField_SerializeTo)
	// @ assert err == nil

	// @ inhale  acc(h_HopField_DecodeFromBytes)
	// @ inhale  len(raw_HopField_DecodeFromBytes) >= HopLen
	// @ inhale acc(sl.Bytes(raw_HopField_DecodeFromBytes, 0, HopLen), R45)
	// @ assume h_HopField_SerializeTo == tmp_h_HopField_SerializeTo
	// @ assume b_HopField_SerializeTo === tmp_b_HopField_SerializeTo
	// @ assume h_HopField_DecodeFromBytes == tmp_h_HopField_DecodeFromBytes
	// @ assume raw_HopField_DecodeFromBytes === tmp_raw_HopField_DecodeFromBytes
	// @ refute false
	err := tmp_h_HopField_DecodeFromBytes.DecodeFromBytes(tmp_b_HopField_SerializeTo)
	// @ assert err == nil
	// @ assert *HopField{IngressRouterAlert:true, EgressRouterAlert:true, ExpTime:0x3f, ConsIngress:0x1, ConsEgress:0x0, Mac:[6]uint8{0x1, 0x2, 0x3, 0x4, 0x5, 0x6}} == tmp_h_HopField_DecodeFromBytes
}
