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
	//@ . "github.com/scionproto/scion/verification/utils/definitions"
	//@ sl "github.com/scionproto/scion/verification/utils/slices"
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

// RegisterPath registers the EPIC path type globally.
// @ requires path.PathPackageMem()
// @ requires !path.Registered(PathType)
// @ ensures  path.PathPackageMem()
// @ ensures  forall t path.Type :: { old(path.Registered(t)) }{ path.Registered(t) } 0 <= t && t < path.MaxPathType ==>
// @ 	t != PathType ==> old(path.Registered(t)) == path.Registered(t)
// @ ensures  path.Registered(PathType)
// @ decreases
func RegisterPath() {
	tmp := path.Metadata{
		Type: PathType,
		Desc: "Epic",
		New:
		//@ ensures p.NonInitMem()
		//@ ensures p != nil
		//@ decreases
		func /*@ newPath @*/ () (p path.Path) {
			epicTmp := &Path{ScionPath: &scion.Raw{}}
			//@ fold epicTmp.ScionPath.Base.NonInitMem()
			//@ fold epicTmp.ScionPath.NonInitMem()
			//@ fold epicTmp.NonInitMem()
			return epicTmp
		},
	}
	//@ proof tmp.New implements path.NewPathSpec {
	//@		return tmp.New() as newPath
	//@ }
	path.RegisterPath(tmp)
}

// Path denotes the EPIC path type header.
type Path struct {
	PktID     PktID
	PHVF      []byte
	LHVF      []byte
	ScionPath *scion.Raw
}

// SerializeTo serializes the Path into buffer b. On failure, an error is returned, otherwise
// SerializeTo will return nil.
// @ preserves acc(p.Mem(ubuf), R1)
// @ preserves sl.Bytes(ubuf, 0, len(ubuf))
// @ preserves sl.Bytes(b, 0, len(b))
// @ ensures   r != nil ==> r.ErrorMem()
// @ ensures   !old(p.hasScionPath(ubuf)) ==> r != nil
// @ ensures   len(b) < old(p.LenSpec(ubuf)) ==> r != nil
// @ ensures   old(p.getPHVFLen(ubuf)) != HVFLen ==> r != nil
// @ ensures   old(p.getLHVFLen(ubuf)) != HVFLen ==> r != nil
// @ decreases
func (p *Path) SerializeTo(b []byte /*@, ghost ubuf []byte @*/) (r error) {
	if len(b) < p.Len( /*@ ubuf @*/ ) {
		return serrors.New("buffer too small to serialize path.", "expected", int(p.Len( /*@ ubuf @*/ )),
			"actual", len(b))
	}
	//@ unfold acc(p.Mem(ubuf), R1)
	//@ defer fold acc(p.Mem(ubuf), R1)
	if len(p.PHVF) != HVFLen {
		return serrors.New("invalid length of PHVF", "expected", int(HVFLen), "actual", int(len(p.PHVF)))
	}
	if len(p.LHVF) != HVFLen {
		return serrors.New("invalid length of LHVF", "expected", int(HVFLen), "actual", int(len(p.LHVF)))
	}
	if p.ScionPath == nil {
		return serrors.New("SCION path is nil")
	}
	//@ sl.SplitByIndex_Bytes(b, 0, len(b), PktIDLen, writePerm)
	//@ sl.Reslice_Bytes(b, 0, PktIDLen, writePerm)
	p.PktID.SerializeTo(b[:PktIDLen])
	//@ sl.Unslice_Bytes(b, 0, PktIDLen, writePerm)
	//@ sl.SplitByIndex_Bytes(b, PktIDLen, len(b), PktIDLen+HVFLen, writePerm)
	//@ sl.Reslice_Bytes(b, PktIDLen, PktIDLen+HVFLen, writePerm)
	//@ unfold sl.Bytes(b[PktIDLen:(PktIDLen+HVFLen)], 0, HVFLen)
	//@ unfold acc(sl.Bytes(p.PHVF, 0, len(p.PHVF)), R2)
	copy(b[PktIDLen:(PktIDLen+HVFLen)], p.PHVF /*@, R3 @*/)
	//@ fold sl.Bytes(b[PktIDLen:(PktIDLen+HVFLen)], 0, HVFLen)
	//@ fold acc(sl.Bytes(p.PHVF, 0, len(p.PHVF)), R2)
	//@ sl.Unslice_Bytes(b, PktIDLen, PktIDLen+HVFLen, writePerm)
	//@ sl.CombineAtIndex_Bytes(b, 0, PktIDLen+HVFLen, PktIDLen, writePerm)
	//@ sl.SplitByIndex_Bytes(b, PktIDLen+HVFLen, len(b), MetadataLen, writePerm)
	//@ sl.Reslice_Bytes(b, PktIDLen+HVFLen, MetadataLen, writePerm)
	//@ unfold acc(sl.Bytes(p.LHVF, 0, len(p.LHVF)), R3)
	//@ unfold sl.Bytes(b[(PktIDLen+HVFLen):MetadataLen], 0, HVFLen)
	copy(b[(PktIDLen+HVFLen):MetadataLen], p.LHVF /*@, R3 @*/)
	//@ fold sl.Bytes(b[(PktIDLen+HVFLen):MetadataLen], 0, HVFLen)
	//@ fold acc(sl.Bytes(p.LHVF, 0, len(p.LHVF)), R3)
	//@ sl.Unslice_Bytes(b, PktIDLen+HVFLen, MetadataLen, writePerm)
	//@ sl.CombineAtIndex_Bytes(b, 0, MetadataLen, PktIDLen+HVFLen, writePerm)
	//@ sl.Reslice_Bytes(b, MetadataLen, len(b), writePerm)
	//@ ghost defer sl.CombineAtIndex_Bytes(b, 0, len(b), MetadataLen, writePerm)
	//@ ghost defer sl.Unslice_Bytes(b, MetadataLen, len(b), writePerm)
	//@ sl.SplitRange_Bytes(ubuf, MetadataLen, len(ubuf), writePerm)
	//@ ghost defer sl.CombineRange_Bytes(ubuf, MetadataLen, len(ubuf), writePerm)
	return p.ScionPath.SerializeTo(b[MetadataLen:] /*@, ubuf[MetadataLen:] @*/)
}

// DecodeFromBytes deserializes the buffer b into the Path. On failure, an error is returned,
// otherwise SerializeTo will return nil.
// @ requires  p.NonInitMem()
// @ preserves acc(sl.Bytes(b, 0, len(b)), R42)
// @ ensures   len(b) < MetadataLen ==> r != nil
// @ ensures   r == nil ==> p.Mem(b)
// @ ensures   r != nil ==> p.NonInitMem() && r.ErrorMem()
// @ decreases
func (p *Path) DecodeFromBytes(b []byte) (r error) {
	if len(b) < MetadataLen {
		return serrors.New("EPIC Path raw too short", "expected", int(MetadataLen), "actual", int(len(b)))
	}
	//@ unfold p.NonInitMem()
	//@ sl.SplitRange_Bytes(b, 0, PktIDLen, R42)
	p.PktID.DecodeFromBytes(b[:PktIDLen])
	//@ sl.CombineRange_Bytes(b, 0, PktIDLen, R42)
	//@ unfold acc(sl.Bytes(b, 0, len(b)), R42)
	p.PHVF = make([]byte, HVFLen)
	p.LHVF = make([]byte, HVFLen)
	//@ assert forall i int :: { &b[PktIDLen:(PktIDLen+HVFLen)][i] } 0 <= i &&
	//@		i < len(b[PktIDLen:(PktIDLen+HVFLen)]) ==>
	//@     &b[PktIDLen:(PktIDLen+HVFLen)][i] == &b[PktIDLen+i]
	copy(p.PHVF, b[PktIDLen:(PktIDLen+HVFLen)] /*@, R42 @*/)
	//@ fold sl.Bytes(p.PHVF, 0, len(p.PHVF))
	//@ assert forall i int :: { &b[(PktIDLen+HVFLen):MetadataLen][i] } 0 <= i &&
	//@		i < len(b[(PktIDLen+HVFLen):MetadataLen]) ==>
	//@     &b[(PktIDLen+HVFLen):MetadataLen][i] == &b[(PktIDLen+HVFLen)+i]
	copy(p.LHVF, b[(PktIDLen+HVFLen):MetadataLen] /*@, R42 @*/)
	//@ fold sl.Bytes(p.LHVF, 0, len(p.LHVF))
	p.ScionPath = &scion.Raw{}
	//@ fold p.ScionPath.Base.NonInitMem()
	//@ fold p.ScionPath.NonInitMem()
	//@ fold acc(sl.Bytes(b, 0, len(b)), R42)
	//@ sl.SplitRange_Bytes(b, MetadataLen, len(b), R42)
	ret := p.ScionPath.DecodeFromBytes(b[MetadataLen:])
	//@ ghost if ret == nil {
	//@ 	fold p.Mem(b)
	//@ } else {
	//@ 	fold p.NonInitMem()
	//@ }
	//@ sl.CombineRange_Bytes(b, MetadataLen, len(b), R42)
	return ret
}

// Reverse reverses the EPIC path. In particular, this means that the SCION path type subheader
// is reversed.
// @ requires p.Mem(ubuf)
// @ preserves sl.Bytes(ubuf, 0, len(ubuf))
// @ ensures  r == nil ==> ret != nil
// @ ensures  r == nil ==> ret.Mem(ubuf)
// @ ensures  r == nil ==> ret != nil
// @ ensures  r != nil ==> r.ErrorMem()
// @ decreases
func (p *Path) Reverse( /*@ ghost ubuf []byte @*/ ) (ret path.Path, r error) {
	//@ unfold p.Mem(ubuf)
	if p.ScionPath == nil {
		//@ fold p.Mem(ubuf)
		return nil, serrors.New("scion subpath must not be nil")
	}
	//@ sl.SplitRange_Bytes(ubuf, MetadataLen, len(ubuf), writePerm)
	revScion, err := p.ScionPath.Reverse( /*@ ubuf[MetadataLen:] @*/ )
	if err != nil {
		// @ sl.CombineRange_Bytes(ubuf, MetadataLen, len(ubuf), writePerm)
		return nil, err
	}
	//@ sl.CombineRange_Bytes(ubuf, MetadataLen, len(ubuf), writePerm)
	ScionPath, ok := revScion.(*scion.Raw)
	if !ok {
		return nil, serrors.New("reversed path of type scion.Raw must not change type")
	}
	p.ScionPath = ScionPath
	//@ fold p.Mem(ubuf)
	return p, nil
}

// Len returns the length of the EPIC path in bytes.
// @ preserves acc(p.Mem(ubuf), R50)
// @ ensures   l == p.LenSpec(ubuf)
// @ decreases
func (p *Path) Len( /*@ ghost ubuf []byte @*/ ) (l int) {
	// @ unfold acc(p.Mem(ubuf), R50)
	// @ defer fold acc(p.Mem(ubuf), R50)
	if p.ScionPath == nil {
		return MetadataLen
	}
	return MetadataLen + p.ScionPath.Len( /*@ ubuf[MetadataLen:] @*/ )
}

// Type returns the EPIC path type identifier.
// @ pure
// @ requires acc(p.Mem(ubuf), _)
// @ ensures  t == PathType
// @ decreases
func (p *Path) Type( /*@ ghost ubuf []byte @*/ ) (t path.Type) {
	return PathType
}

// PktID denotes the EPIC packet ID.
type PktID struct {
	Timestamp uint32
	Counter   uint32
}

// DecodeFromBytes deserializes the buffer (raw) into the PktID.
// @ requires  len(raw) >= PktIDLen
// @ preserves acc(i)
// @ preserves acc(sl.Bytes(raw, 0, len(raw)), R42)
// @ ensures   0 <= i.Timestamp
// @ ensures   0 <= i.Counter
// @ decreases
func (i *PktID) DecodeFromBytes(raw []byte) {
	//@ unfold acc(sl.Bytes(raw, 0, len(raw)), R42)
	//@ assert forall i int :: { &raw[:4][i] } 0 <= i && i < 4 ==> &raw[:4][i] == &raw[i]
	i.Timestamp = binary.BigEndian.Uint32(raw[:4])
	//@ assert forall i int :: { &raw[4:8][i] } 0 <= i && i < 4 ==> &raw[4:8][i] == &raw[4 + i]
	i.Counter = binary.BigEndian.Uint32(raw[4:8])
	//@ fold acc(sl.Bytes(raw, 0, len(raw)), R42)
}

// SerializeTo serializes the PktID into the buffer (b).
// @ requires  len(b) >= PktIDLen
// @ preserves acc(i, R1)
// @ preserves sl.Bytes(b, 0, len(b))
// @ decreases
func (i *PktID) SerializeTo(b []byte) {
	//@ unfold sl.Bytes(b, 0, len(b))
	//@ assert forall j int :: { &b[:4][j] } 0 <= 4 ==> &b[:4][j] == &b[j]
	binary.BigEndian.PutUint32(b[:4], i.Timestamp)
	//@ assert forall j int :: { &b[4:8][j] } 0 <= 4 ==> &b[4:8][j] == &b[4 + j]
	binary.BigEndian.PutUint32(b[4:8], i.Counter)
	//@ fold sl.Bytes(b, 0, len(b))
}
