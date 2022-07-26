// Copyright 2020 ETH Zurich
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//   http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

// +gobra

// Package epic implements the Path interface for the EPIC path type.
package epic

import (
	"encoding/binary"

	"github.com/scionproto/scion/pkg/private/serrors"
	"github.com/scionproto/scion/pkg/slayers/path"
	"github.com/scionproto/scion/pkg/slayers/path/scion"
	//@ "github.com/scionproto/scion/verification/utils/definitions"
	//@ "github.com/scionproto/scion/verification/utils/slices"
)

const (
	// PathType denotes the EPIC path type identifier.
	PathType path.Type = 3
	// MetadataLen denotes the number of bytes the EPIC path type contains in addition to the SCION
	// path type. It is the sum of the PktID (8B), the PHVF (4B) and the LHVF (4B) sizes.
	MetadataLen = 16
	// PktIDLen denotes the length of the packet identifier.
	PktIDLen = 8
	// HVFLen denotes the length of the hop validation fields. The length is the same for both the
	// PHVF and the LHVF.
	HVFLen = 4
)

/*
// RegisterPath registers the EPIC path type globally.
func RegisterPath() {
	path.RegisterPath(path.Metadata{
		Type: PathType,
		Desc: "Epic",
		New: func() path.Path {
			return &Path{ScionPath: &scion.Raw{}}
		},
	})
}
*/

// Path denotes the EPIC path type header.
type Path struct {
	PktID     PktID
	PHVF      []byte
	LHVF      []byte
	ScionPath *scion.Raw
}

// SerializeTo serializes the Path into buffer b. On failure, an error is returned, otherwise
// SerializeTo will return nil.
// requires acc(p.Mem(), definitions.ReadL1)
//@ requires  p.Mem()
//@ requires  p.hasScionPath()
//@ requires  len(b) >= p.Len()
//@ requires  p.getPHVFLen() == HVFLen
//@ requires  p.getLHVFLen() == HVFLen
//@ preserves slices.AbsSlice_Bytes(b, 0, len(b))
//@ ensures   p.Mem()
// ensures acc(p.Mem(), definitions.ReadL1)
//@ decreases
func (p *Path) SerializeTo(b []byte) error {
	if len(b) < p.Len() {
		return serrors.New("buffer too small to serialize path.", "expected", p.Len(),
			"actual", len(b))
	}
	//@ unfold p.Mem()
	if len(p.PHVF) != HVFLen {
		//@ fold p.Mem()
		return serrors.New("invalid length of PHVF", "expected", HVFLen, "actual", len(p.PHVF))
	}
	if len(p.LHVF) != HVFLen {
		//@ fold p.Mem()
		return serrors.New("invalid length of LHVF", "expected", HVFLen, "actual", len(p.LHVF))
	}
	if p.ScionPath == nil {
		//@ fold p.Mem()
		return serrors.New("SCION path is nil")
	}
	//@ ghost slices.SplitByIndex_Bytes(b, 0, len(b), PktIDLen, writePerm)
	//@ ghost slices.Reslice_Bytes(b, 0, PktIDLen, writePerm)
	p.PktID.SerializeTo(b[:PktIDLen])
	//@ ghost slices.Unslice_Bytes(b, 0, PktIDLen, writePerm)
	//@ ghost slices.SplitByIndex_Bytes(b, PktIDLen, len(b), PktIDLen+HVFLen, writePerm)
	//@ preserves slices.AbsSlice_Bytes(b, PktIDLen, PktIDLen + HVFLen)
	//@ preserves acc(&p.PHVF)
	//@ preserves forall i int :: 0 <= i && i < len(p.PHVF) ==> acc(&p.PHVF[i])
	//@ decreases
	//@ outline(
	//@ ghost slices.Reslice_Bytes(b, PktIDLen, PktIDLen+HVFLen, writePerm)
	//@ assert len(b[PktIDLen:(PktIDLen+HVFLen)]) == HVFLen
	//@ unfold slices.AbsSlice_Bytes(b[PktIDLen:(PktIDLen+HVFLen)], 0, HVFLen)
	copy(b[PktIDLen:(PktIDLen+HVFLen)], p.PHVF /*@, definitions.ReadL1 @*/)
	//@ fold slices.AbsSlice_Bytes(b[PktIDLen:(PktIDLen+HVFLen)], 0, HVFLen)
	//@ ghost slices.Unslice_Bytes(b, PktIDLen, PktIDLen+HVFLen, writePerm)
	//@ )
	//@ ghost slices.CombineAtIndex_Bytes(b, 0, PktIDLen+HVFLen, PktIDLen, writePerm)
	//@ ghost slices.SplitByIndex_Bytes(b, PktIDLen+HVFLen, len(b), MetadataLen, writePerm)
	//@ preserves slices.AbsSlice_Bytes(b, PktIDLen+HVFLen, MetadataLen)
	//@ preserves acc(&p.LHVF)
	//@ preserves forall i int :: 0 <= i && i < len(p.LHVF) ==> acc(&p.LHVF[i])
	//@ decreases
	//@ outline(
	//@ ghost slices.Reslice_Bytes(b, PktIDLen+HVFLen, MetadataLen, writePerm)
	//@ assert len(b[(PktIDLen+HVFLen):MetadataLen]) == HVFLen
	//@ unfold slices.AbsSlice_Bytes(b[(PktIDLen+HVFLen):MetadataLen], 0, HVFLen)
	copy(b[(PktIDLen+HVFLen):MetadataLen], p.LHVF /*@, definitions.ReadL1 @*/)
	//@ fold slices.AbsSlice_Bytes(b[(PktIDLen+HVFLen):MetadataLen], 0, HVFLen)
	//@ ghost slices.Unslice_Bytes(b, PktIDLen+HVFLen, MetadataLen, writePerm)
	//@ )
	//@ ghost slices.CombineAtIndex_Bytes(b, 0, MetadataLen, PktIDLen+HVFLen, writePerm)
	//@ ghost slices.Reslice_Bytes(b, MetadataLen, len(b), writePerm)
	ret := p.ScionPath.SerializeTo(b[MetadataLen:])
	//@ ghost slices.Unslice_Bytes(b, MetadataLen, len(b), writePerm)
	//@ ghost slices.CombineAtIndex_Bytes(b, 0, len(b), MetadataLen, writePerm)
	//@ fold p.Mem()
	return ret
}

// DecodeFromBytes deserializes the buffer b into the Path. On failure, an error is returned,
// otherwise SerializeTo will return nil.
//@ requires  p.NonInitMem()
//@ requires  len(b) >= MetadataLen + scion.MetaLen
//@ requires slices.AbsSlice_Bytes(b, 0, len(b))
//@ ensures slices.AbsSlice_Bytes(b, 0, MetadataLen)
//@ ensures r == nil ==> p.Mem()
//@ ensures r != nil ==> p.NonInitMem()
//@ decreases
func (p *Path) DecodeFromBytes(b []byte) (r error) {
	if len(b) < MetadataLen {
		return serrors.New("EPIC Path raw too short", "expected", MetadataLen, "actual", len(b))
	}
	//@ assert MetadataLen == PktIDLen + HVFLen + HVFLen
	//@ unfold p.NonInitMem()
	//@ ghost slices.SplitByIndex_Bytes(b, 0, len(b), PktIDLen, writePerm)
	//@ ghost slices.Reslice_Bytes(b, 0, PktIDLen, writePerm)
	p.PktID.DecodeFromBytes(b[:PktIDLen])
	p.PHVF = make([]byte, HVFLen)
	p.LHVF = make([]byte, HVFLen)
	//@ ghost slices.Unslice_Bytes(b, 0, PktIDLen, writePerm)
	//@ ghost slices.SplitByIndex_Bytes(b, PktIDLen, len(b), PktIDLen+HVFLen, writePerm)
	//@ preserves acc(&p.PHVF)
	//@ preserves forall i int :: 0 <= i && i < len(p.PHVF) ==> acc(&p.PHVF[i])
	//@ preserves slices.AbsSlice_Bytes(b, PktIDLen, PktIDLen + HVFLen)
	//@ decreases
	//@ outline(
	//@ ghost slices.Reslice_Bytes(b, PktIDLen, PktIDLen+HVFLen, writePerm)
	//@ unfold acc(slices.AbsSlice_Bytes(b[PktIDLen:(PktIDLen+HVFLen)], 0, HVFLen), definitions.ReadL1)
	copy(p.PHVF, b[PktIDLen:(PktIDLen+HVFLen)] /*@, definitions.ReadL1 @*/)
	//@ fold acc(slices.AbsSlice_Bytes(b[PktIDLen:(PktIDLen+HVFLen)], 0, HVFLen), definitions.ReadL1)
	//@ ghost slices.Unslice_Bytes(b, PktIDLen, PktIDLen+HVFLen, writePerm)
	//@ )
	//@ ghost slices.CombineAtIndex_Bytes(b, 0, PktIDLen+HVFLen, PktIDLen, writePerm)
	//@ ghost slices.SplitByIndex_Bytes(b, PktIDLen+HVFLen, len(b), MetadataLen, writePerm)
	//@ preserves acc(&p.LHVF)
	//@ preserves forall i int :: 0 <= i && i < len(p.LHVF) ==> acc(&p.LHVF[i])
	//@ preserves slices.AbsSlice_Bytes(b, PktIDLen+HVFLen, MetadataLen)
	//@ decreases
	//@ outline(
	//@ ghost slices.Reslice_Bytes(b, PktIDLen+HVFLen, MetadataLen, writePerm)
	//@ unfold acc(slices.AbsSlice_Bytes(b[PktIDLen+HVFLen:MetadataLen], 0, HVFLen), definitions.ReadL1)
	copy(p.LHVF, b[(PktIDLen+HVFLen):MetadataLen] /*@, definitions.ReadL1 @*/)
	//@ fold acc(slices.AbsSlice_Bytes(b[PktIDLen+HVFLen:MetadataLen], 0, HVFLen), definitions.ReadL1)
	//@ ghost slices.Unslice_Bytes(b, PktIDLen+HVFLen, MetadataLen, writePerm)
	//@ )
	//@ ghost slices.CombineAtIndex_Bytes(b, 0, MetadataLen, PktIDLen+HVFLen, writePerm)
	p.ScionPath = &scion.Raw{}
	//@ fold p.ScionPath.Base.NonInitMem()
	//@ fold p.ScionPath.NonInitMem()
	//@ ghost slices.Reslice_Bytes(b, MetadataLen, len(b), writePerm)
	ret := p.ScionPath.DecodeFromBytes(b[MetadataLen:])
	//@ ghost if ret == nil {
	//@   fold p.Mem()
	//@ } else {
	//@   fold p.NonInitMem()
	//@ }
	return ret
}

// Reverse reverses the EPIC path. In particular, this means that the SCION path type subheader
// is reversed.
//@ trusted // TODO
//@ requires p.Mem()
//@ ensures r == nil ==> p.Mem()
//@ ensures r != nil ==> ret.Mem()
//@ decreases
func (p *Path) Reverse() (ret path.Path, r error) {
	//@ unfold p.Mem()
	if p.ScionPath == nil {
		//@ fold p.Mem()
		return nil, serrors.New("scion subpath must not be nil")
	}
	//@ assert p.ScionPath.Mem()
	revScion, err := p.ScionPath.Reverse()
	if err != nil {
		return nil, err
	}
	//@ assert revScion.Mem()
	ScionPath, ok := revScion.(*scion.Raw)
	if !ok {
		return nil, serrors.New("reversed path of type scion.Raw must not change type")
	}
	//@ assert ScionPath.Mem()
	p.ScionPath = ScionPath
	//@ fold p.Mem()
	return p, nil
}

// Len returns the length of the EPIC path in bytes.
// TODO How do we get around the if statement in a pure func
//@ trusted
//@ pure
//@ requires acc(p.Mem(), _)
//@ requires p.hasScionPath()
// ensures   unfolding acc(p.Mem(), _) in (p.ScionPath == nil ==> (l == MetadataLen))
// ensures   unfolding acc(p.Mem(), _) in (p.ScionPath != nil ==> (l == MetadataLen + p.ScionPath.RawLen()))
//@ ensures  unfolding acc(p.Mem(), _) in (l == MetadataLen + p.ScionPath.RawLen())
//@ decreases
func (p *Path) Len() (l int) {
	if p.ScionPath == nil {
		return MetadataLen
	}
	return /*@ unfolding acc(p.Mem(), _) in unfolding p.ScionPath.Mem() in @*/ MetadataLen + p.ScionPath.Len()
}

// Type returns the EPIC path type identifier.
//@ pure
//@ requires acc(p.Mem(), _)
//@ ensures t == PathType
//@ decreases
func (p *Path) Type() (t path.Type) {
	return PathType
}

// PktID denotes the EPIC packet ID.
type PktID struct {
	Timestamp uint32
	Counter   uint32
}

// DecodeFromBytes deserializes the buffer (raw) into the PktID.
//@ requires  len(raw) >= PktIDLen
//@ preserves acc(i)
//@ preserves acc(slices.AbsSlice_Bytes(raw, 0, len(raw)), definitions.ReadL1)
//@ ensures 0 <= i.Timestamp
//@ ensures 0 <= i.Counter
//@ decreases
func (i *PktID) DecodeFromBytes(raw []byte) {
	//@ unfold acc(slices.AbsSlice_Bytes(raw, 0, len(raw)), definitions.ReadL1)
	//@ assert forall i int :: 0 <= i && i < 4 ==>
	//@   &raw[:4][i] == &raw[i]
	i.Timestamp = binary.BigEndian.Uint32(raw[:4])
	//@ assert forall i int :: 0 <= i && i < 4 ==>
	//@   &raw[4:8][i] == &raw[4 + i]
	i.Counter = binary.BigEndian.Uint32(raw[4:8])
	// (gavin) TODO why are these assumptions still needed?
	// The post-condition of Uint32 is that the result is >= 0
	// yet if the following are not present Gobra complains.
	//@ assume i.Counter >= 0
	//@ assume i.Timestamp >= 0
	//@ fold acc(slices.AbsSlice_Bytes(raw, 0, len(raw)), definitions.ReadL1)
}

// SerializeTo serializes the PktID into the buffer (b).
//@ requires  len(b) >= PktIDLen
//@ preserves acc(i, definitions.ReadL1)
//@ preserves slices.AbsSlice_Bytes(b, 0, len(b))
//@ decreases
func (i *PktID) SerializeTo(b []byte) {
	//@ unfold slices.AbsSlice_Bytes(b, 0, len(b))
	//@ assert forall j int :: 0 <= 4 ==>
	//@   &b[:4][j] == &b[j]
	binary.BigEndian.PutUint32(b[:4], i.Timestamp)
	//@ assert forall j int :: 0 <= 4 ==>
	//@   &b[4:8][j] == &b[4 + j]
	binary.BigEndian.PutUint32(b[4:8], i.Counter)
	//@ fold slices.AbsSlice_Bytes(b, 0, len(b))
}
