package epic

import (
	"github.com/scionproto/scion/pkg/slayers/path/scion"
	// @ . "github.com/scionproto/scion/verification/utils/definitions"
	// @ sl "github.com/scionproto/scion/verification/utils/slices"
	"fmt"
	"github.com/scionproto/scion/assertion"
)

func TestSerialize_SCION_path_nil(p_Path_SerializeTo *Path, b_Path_SerializeTo []byte, ghost_ubuf_SerializeTo []byte) {
	var tmp_p_Path_SerializeTo *Path
	var tmp_b_Path_SerializeTo []byte
	var tmp_ghost_ubuf_SerializeTo []byte
	tmp_p_Path_SerializeTo = &Path{PktID: PktID{Timestamp: 1, Counter: 33554435}, PHVF: []uint8{0x1, 0x2, 0x3, 0x4}, LHVF: []uint8{0x5, 0x6, 0x7, 0x8}, ScionPath: nil}
	tmp_b_Path_SerializeTo = []uint8{}
	// @ inhale acc(p_Path_SerializeTo.Mem(ghost_ubuf_SerializeTo), R1)
	// @ inhale sl.Bytes(ghost_ubuf_SerializeTo, 0, len(ghost_ubuf_SerializeTo))
	// @ inhale sl.Bytes(b_Path_SerializeTo, 0, len(b_Path_SerializeTo))
	// @ exhale acc(tmp_p_Path_SerializeTo)
	// @ assume p_Path_SerializeTo == tmp_p_Path_SerializeTo
	// @ assume b_Path_SerializeTo === tmp_b_Path_SerializeTo
	err := p_Path_SerializeTo.SerializeTo(b_Path_SerializeTo /*@ , ghost_ubuf_SerializeTo @*/)
	// @ unfold acc(p_Path_SerializeTo.Mem(ghost_ubuf_SerializeTo), R1)
	// @ unfold sl.Bytes(ghost_ubuf_SerializeTo, 0, len(ghost_ubuf_SerializeTo))
	// @ unfold sl.Bytes(b_Path_SerializeTo, 0, len(b_Path_SerializeTo))
	// @ ass0_Path_SerializeTo := err != nil
	// @ assert ass0_Path_SerializeTo
	// @ fold acc(p_Path_SerializeTo.Mem(ghost_ubuf_SerializeTo), R1)
	// @ fold sl.Bytes(ghost_ubuf_SerializeTo, 0, len(ghost_ubuf_SerializeTo))
	// @ fold sl.Bytes(b_Path_SerializeTo, 0, len(b_Path_SerializeTo))
}
func TestSerialize_Basic(p_Path_SerializeTo *Path, b_Path_SerializeTo []byte, ghost_ubuf_SerializeTo []byte) {
	var tmp_p_Path_SerializeTo *Path
	var tmp_b_Path_SerializeTo []byte
	var tmp_ghost_ubuf_SerializeTo []byte
	tmp_p_Path_SerializeTo = &Path{PktID: PktID{Timestamp: 1, Counter: 33554435}, PHVF: []uint8{0x1, 0x2, 0x3, 0x4}, LHVF: []uint8{0x5, 0x6, 0x7, 0x8}, ScionPath: &scion.Raw{Base: scion.Base{PathMeta: scion.MetaHdr{CurrINF: 0, CurrHF: 0, SegLen: [3]uint8{0x2, 0x2, 0x0}}, NumINF: 2, NumHops: 4}, Raw: []uint8{0x0, 0x0, 0x20, 0x80, 0x0, 0x0, 0x1, 0x11, 0x0, 0x0, 0x1, 0x0, 0x1, 0x0, 0x2, 0x22, 0x0, 0x0, 0x1, 0x0, 0x0, 0x3f, 0x0, 0x1, 0x0, 0x0, 0x1, 0x2, 0x3, 0x4, 0x5, 0x6, 0x0, 0x3f, 0x0, 0x3, 0x0, 0x2, 0x1, 0x2, 0x3, 0x4, 0x5, 0x6, 0x0, 0x3f, 0x0, 0x0, 0x0, 0x2, 0x1, 0x2, 0x3, 0x4, 0x5, 0x6, 0x0, 0x3f, 0x0, 0x1, 0x0, 0x0, 0x1, 0x2, 0x3, 0x4, 0x5, 0x6}}}
	tmp_b_Path_SerializeTo = []uint8{0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0}
	// @ inhale acc(p_Path_SerializeTo.Mem(ghost_ubuf_SerializeTo), R1)
	// @ inhale sl.Bytes(ghost_ubuf_SerializeTo, 0, len(ghost_ubuf_SerializeTo))
	// @ inhale sl.Bytes(b_Path_SerializeTo, 0, len(b_Path_SerializeTo))
	// @ exhale acc(tmp_p_Path_SerializeTo)
	// @ assume p_Path_SerializeTo == tmp_p_Path_SerializeTo
	// @ assume b_Path_SerializeTo === tmp_b_Path_SerializeTo
	// @ refute false
	err := p_Path_SerializeTo.SerializeTo(b_Path_SerializeTo /*@ , ghost_ubuf_SerializeTo @*/)
	// @ unfold acc(p_Path_SerializeTo.Mem(ghost_ubuf_SerializeTo), R1)
	// @ unfold sl.Bytes(ghost_ubuf_SerializeTo, 0, len(ghost_ubuf_SerializeTo))
	// @ unfold sl.Bytes(b_Path_SerializeTo, 0, len(b_Path_SerializeTo))
	// @ ass0_Path_SerializeTo := err == nil
	// @ assert ass0_Path_SerializeTo
	// @ ass1_Path_SerializeTo := assertion.EqualSliceByte([]byte{0x0, 0x0, 0x0, 0x1, 0x2, 0x0, 0x0, 0x3, 0x1, 0x2, 0x3, 0x4, 0x5, 0x6, 0x7, 0x8, 0x0, 0x0, 0x20, 0x80, 0x0, 0x0, 0x1, 0x11, 0x0, 0x0, 0x1, 0x0, 0x1, 0x0, 0x2, 0x22, 0x0, 0x0, 0x1, 0x0, 0x0, 0x3f, 0x0, 0x1, 0x0, 0x0, 0x1, 0x2, 0x3, 0x4, 0x5, 0x6, 0x0, 0x3f, 0x0, 0x3, 0x0, 0x2, 0x1, 0x2, 0x3, 0x4, 0x5, 0x6, 0x0, 0x3f, 0x0, 0x0, 0x0, 0x2, 0x1, 0x2, 0x3, 0x4, 0x5, 0x6, 0x0, 0x3f, 0x0, 0x1, 0x0, 0x0, 0x1, 0x2, 0x3, 0x4, 0x5, 0x6} ,  b_Path_SerializeTo)
	// @ assert ass1_Path_SerializeTo
	// @ fold acc(p_Path_SerializeTo.Mem(ghost_ubuf_SerializeTo), R1)
	// @ fold sl.Bytes(ghost_ubuf_SerializeTo, 0, len(ghost_ubuf_SerializeTo))
	// @ fold sl.Bytes(b_Path_SerializeTo, 0, len(b_Path_SerializeTo))
}
func TestSerialize_HVF_too_short(p_Path_SerializeTo *Path, b_Path_SerializeTo []byte, ghost_ubuf_SerializeTo []byte) {
	var tmp_p_Path_SerializeTo *Path
	var tmp_b_Path_SerializeTo []byte
	var tmp_ghost_ubuf_SerializeTo []byte
	tmp_p_Path_SerializeTo = &Path{PktID: PktID{Timestamp: 1, Counter: 33554435}, PHVF: []uint8{0x1, 0x2, 0x3}, LHVF: []uint8{0x5, 0x6, 0x7, 0x8}, ScionPath: &scion.Raw{Base: scion.Base{PathMeta: scion.MetaHdr{CurrINF: 0, CurrHF: 0, SegLen: [3]uint8{0x2, 0x2, 0x0}}, NumINF: 2, NumHops: 4}, Raw: []uint8{0x0, 0x0, 0x20, 0x80, 0x0, 0x0, 0x1, 0x11, 0x0, 0x0, 0x1, 0x0, 0x1, 0x0, 0x2, 0x22, 0x0, 0x0, 0x1, 0x0, 0x0, 0x3f, 0x0, 0x1, 0x0, 0x0, 0x1, 0x2, 0x3, 0x4, 0x5, 0x6, 0x0, 0x3f, 0x0, 0x3, 0x0, 0x2, 0x1, 0x2, 0x3, 0x4, 0x5, 0x6, 0x0, 0x3f, 0x0, 0x0, 0x0, 0x2, 0x1, 0x2, 0x3, 0x4, 0x5, 0x6, 0x0, 0x3f, 0x0, 0x1, 0x0, 0x0, 0x1, 0x2, 0x3, 0x4, 0x5, 0x6}}}
	tmp_b_Path_SerializeTo = []uint8{}
	// @ inhale acc(p_Path_SerializeTo.Mem(ghost_ubuf_SerializeTo), R1)
	// @ inhale sl.Bytes(ghost_ubuf_SerializeTo, 0, len(ghost_ubuf_SerializeTo))
	// @ inhale sl.Bytes(b_Path_SerializeTo, 0, len(b_Path_SerializeTo))
	// @ exhale acc(tmp_p_Path_SerializeTo)
	// @ assume p_Path_SerializeTo == tmp_p_Path_SerializeTo
	// @ assume b_Path_SerializeTo === tmp_b_Path_SerializeTo
	err := p_Path_SerializeTo.SerializeTo(b_Path_SerializeTo /*@ , ghost_ubuf_SerializeTo @*/)
	// @ unfold acc(p_Path_SerializeTo.Mem(ghost_ubuf_SerializeTo), R1)
	// @ unfold sl.Bytes(ghost_ubuf_SerializeTo, 0, len(ghost_ubuf_SerializeTo))
	// @ unfold sl.Bytes(b_Path_SerializeTo, 0, len(b_Path_SerializeTo))
	// @ ass0_Path_SerializeTo := err != nil
	// @ assert ass0_Path_SerializeTo
	// @ fold acc(p_Path_SerializeTo.Mem(ghost_ubuf_SerializeTo), R1)
	// @ fold sl.Bytes(ghost_ubuf_SerializeTo, 0, len(ghost_ubuf_SerializeTo))
	// @ fold sl.Bytes(b_Path_SerializeTo, 0, len(b_Path_SerializeTo))
}
func TestSerialize_HVF_too_long(p_Path_SerializeTo *Path, b_Path_SerializeTo []byte, ghost_ubuf_SerializeTo []byte) {
	var tmp_p_Path_SerializeTo *Path
	var tmp_b_Path_SerializeTo []byte
	var tmp_ghost_ubuf_SerializeTo []byte
	tmp_p_Path_SerializeTo = &Path{PktID: PktID{Timestamp: 1, Counter: 33554435}, PHVF: []uint8{0x1, 0x2, 0x3, 0x4}, LHVF: []uint8{0x5, 0x6, 0x7, 0x8, 0x9}, ScionPath: &scion.Raw{Base: scion.Base{PathMeta: scion.MetaHdr{CurrINF: 0, CurrHF: 0, SegLen: [3]uint8{0x2, 0x2, 0x0}}, NumINF: 2, NumHops: 4}, Raw: []uint8{0x0, 0x0, 0x20, 0x80, 0x0, 0x0, 0x1, 0x11, 0x0, 0x0, 0x1, 0x0, 0x1, 0x0, 0x2, 0x22, 0x0, 0x0, 0x1, 0x0, 0x0, 0x3f, 0x0, 0x1, 0x0, 0x0, 0x1, 0x2, 0x3, 0x4, 0x5, 0x6, 0x0, 0x3f, 0x0, 0x3, 0x0, 0x2, 0x1, 0x2, 0x3, 0x4, 0x5, 0x6, 0x0, 0x3f, 0x0, 0x0, 0x0, 0x2, 0x1, 0x2, 0x3, 0x4, 0x5, 0x6, 0x0, 0x3f, 0x0, 0x1, 0x0, 0x0, 0x1, 0x2, 0x3, 0x4, 0x5, 0x6}}}
	tmp_b_Path_SerializeTo = []uint8{}
	// @ inhale acc(p_Path_SerializeTo.Mem(ghost_ubuf_SerializeTo), R1)
	// @ inhale sl.Bytes(ghost_ubuf_SerializeTo, 0, len(ghost_ubuf_SerializeTo))
	// @ inhale sl.Bytes(b_Path_SerializeTo, 0, len(b_Path_SerializeTo))
	// @ exhale acc(tmp_p_Path_SerializeTo)
	// @ assume p_Path_SerializeTo == tmp_p_Path_SerializeTo
	// @ assume b_Path_SerializeTo === tmp_b_Path_SerializeTo
	err := p_Path_SerializeTo.SerializeTo(b_Path_SerializeTo /*@ , ghost_ubuf_SerializeTo @*/)
	// @ unfold acc(p_Path_SerializeTo.Mem(ghost_ubuf_SerializeTo), R1)
	// @ unfold sl.Bytes(ghost_ubuf_SerializeTo, 0, len(ghost_ubuf_SerializeTo))
	// @ unfold sl.Bytes(b_Path_SerializeTo, 0, len(b_Path_SerializeTo))
	// @ ass0_Path_SerializeTo := err != nil
	// @ assert ass0_Path_SerializeTo
	// @ fold acc(p_Path_SerializeTo.Mem(ghost_ubuf_SerializeTo), R1)
	// @ fold sl.Bytes(ghost_ubuf_SerializeTo, 0, len(ghost_ubuf_SerializeTo))
	// @ fold sl.Bytes(b_Path_SerializeTo, 0, len(b_Path_SerializeTo))
}
