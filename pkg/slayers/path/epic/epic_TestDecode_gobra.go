package epic

import (
	"github.com/scionproto/scion/pkg/slayers/path/scion"
	// @ . "github.com/scionproto/scion/verification/utils/definitions"
	// @ sl "github.com/scionproto/scion/verification/utils/slices"
	"fmt"
	"github.com/scionproto/scion/assertion"
)

func TestDecode_Basic(p_Path_DecodeFromBytes *Path, b_Path_DecodeFromBytes []byte) {
	var tmp_p_Path_DecodeFromBytes *Path
	var tmp_b_Path_DecodeFromBytes []byte
	tmp_p_Path_DecodeFromBytes = &Path{PktID: PktID{Timestamp: 0, Counter: 0}, PHVF: []uint8(nil), LHVF: []uint8(nil), ScionPath: nil}
	tmp_b_Path_DecodeFromBytes = []uint8{0x0, 0x0, 0x0, 0x1, 0x2, 0x0, 0x0, 0x3, 0x1, 0x2, 0x3, 0x4, 0x5, 0x6, 0x7, 0x8, 0x0, 0x0, 0x20, 0x80, 0x0, 0x0, 0x1, 0x11, 0x0, 0x0, 0x1, 0x0, 0x1, 0x0, 0x2, 0x22, 0x0, 0x0, 0x1, 0x0, 0x0, 0x3f, 0x0, 0x1, 0x0, 0x0, 0x1, 0x2, 0x3, 0x4, 0x5, 0x6, 0x0, 0x3f, 0x0, 0x3, 0x0, 0x2, 0x1, 0x2, 0x3, 0x4, 0x5, 0x6, 0x0, 0x3f, 0x0, 0x0, 0x0, 0x2, 0x1, 0x2, 0x3, 0x4, 0x5, 0x6, 0x0, 0x3f, 0x0, 0x1, 0x0, 0x0, 0x1, 0x2, 0x3, 0x4, 0x5, 0x6}
	// @ inhale  p_Path_DecodeFromBytes.NonInitMem()
	// @ inhale acc(sl.Bytes(b_Path_DecodeFromBytes, 0, len(b_Path_DecodeFromBytes)), R42)
	// @ exhale acc(tmp_p_Path_DecodeFromBytes)
	// @ assume p_Path_DecodeFromBytes == tmp_p_Path_DecodeFromBytes
	// @ assume b_Path_DecodeFromBytes === tmp_b_Path_DecodeFromBytes
	// @ refute false
	err := p_Path_DecodeFromBytes.DecodeFromBytes(b_Path_DecodeFromBytes)
	// @ unfold acc(sl.Bytes(b_Path_DecodeFromBytes, 0, len(b_Path_DecodeFromBytes)), R42)
	// @ unfold p_Path_DecodeFromBytes.Mem(b_Path_DecodeFromBytes)
	// @ ass0_Path_DecodeFromBytes := err == nil
	// @ assert ass0_Path_DecodeFromBytes
	// @ ass1_Path_DecodeFromBytes := Path{PktID:PktID{Timestamp:0x1, Counter:0x2000003}, PHVF:[]uint8{0x1, 0x2, 0x3, 0x4}, LHVF:[]uint8{0x5, 0x6, 0x7, 0x8}, ScionPath:(*scion.Raw)(0xb5b1a0)} == *p_Path_DecodeFromBytes
	// @ assert ass1_Path_DecodeFromBytes
	// @ fold acc(sl.Bytes(b_Path_DecodeFromBytes, 0, len(b_Path_DecodeFromBytes)), R42)
	// @ fold p_Path_DecodeFromBytes.Mem(b_Path_DecodeFromBytes)
}
