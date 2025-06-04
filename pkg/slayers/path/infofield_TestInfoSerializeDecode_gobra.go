package path

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
	// @ inhale slices.Bytes(b_InfoField_SerializeTo, 0, len(b_InfoField_SerializeTo))
	// @ assume inf_InfoField_SerializeTo == tmp_inf_InfoField_SerializeTo
	// @ assume b_InfoField_SerializeTo === tmp_b_InfoField_SerializeTo
	// @ assume inf_InfoField_DecodeFromBytes == tmp_inf_InfoField_DecodeFromBytes
	// @ assume raw_InfoField_DecodeFromBytes === tmp_raw_InfoField_DecodeFromBytes
	// @ refute false
	err := tmp_inf_InfoField_SerializeTo.SerializeTo(tmp_b_InfoField_SerializeTo)
	// @ assert err == nil

	// @ inhale  len(raw_InfoField_DecodeFromBytes) >= InfoLen
	// @ inhale acc(inf_InfoField_DecodeFromBytes)
	// @ inhale acc(slices.Bytes(raw_InfoField_DecodeFromBytes, 0, len(raw_InfoField_DecodeFromBytes)), R45)
	// @ assume inf_InfoField_SerializeTo == tmp_inf_InfoField_SerializeTo
	// @ assume b_InfoField_SerializeTo === tmp_b_InfoField_SerializeTo
	// @ assume inf_InfoField_DecodeFromBytes == tmp_inf_InfoField_DecodeFromBytes
	// @ assume raw_InfoField_DecodeFromBytes === tmp_raw_InfoField_DecodeFromBytes
	// @ refute false
	err := tmp_inf_InfoField_DecodeFromBytes.DecodeFromBytes(tmp_b_InfoField_SerializeTo)
	// @ assert err == nil
	// @ assert *InfoField{Peer:true, ConsDir:true, SegID:0x222, Timestamp:0x100} == tmp_inf_InfoField_DecodeFromBytes
}
