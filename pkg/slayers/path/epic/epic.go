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
//@ requires  len(b) >= p.Len()
//@ requires  p.getPHVFLen() == HVFLen
//@ requires  p.getLHVFLen() == HVFLen
//@ preserves forall i int :: 0 <= i && i < len(b) ==>
//@   acc(&b[i])
//@ ensures p.Mem()
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
	//@ assert p.ScionPath.Mem()
	//@ assert len(b[:PktIDLen]) == PktIDLen
	p.PktID.SerializeTo(b[:PktIDLen])
	//@ assert acc(p.PHVF, definitions.ReadL1)
	//@ assert len(b[PktIDLen:(PktIDLen+HVFLen)]) == HVFLen
	//@ assert forall i int :: 0 <= i && i < HVFLen ==>
	//@   &b[PktIDLen:(PktIDLen+HVFLen)][i] == &b[PktIDLen + i]
	copy(b[PktIDLen:(PktIDLen+HVFLen)], p.PHVF /*@, definitions.ReadL1 @*/)
	//@ assert acc(p.LHVF, definitions.ReadL1)
	//@ assert len(b[(PktIDLen+HVFLen):MetadataLen]) == HVFLen
	//@ assert forall i int :: 0 <= i && i < HVFLen ==>
	//@   &b[(PktIDLen+HVFLen):MetadataLen][i] == &b[PktIDLen + HVFLen + i]
	copy(b[(PktIDLen+HVFLen):MetadataLen], p.LHVF /*@, definitions.ReadL1 @*/)
	//@ assert p.ScionPath.Mem()
	//@ assert MetadataLen <= len(b)
	//@ assert forall i int :: 0 <= i && i < len(b) - MetadataLen ==>
	//@   &b[MetadataLen:][i] == &b[MetadataLen + i]
	ret := p.ScionPath.SerializeTo(b[MetadataLen:])
	//@ fold p.Mem()
	return ret
}

// DecodeFromBytes deserializes the buffer b into the Path. On failure, an error is returned,
// otherwise SerializeTo will return nil.
//@ requires  p.NonInitMem()
//@ requires  len(b) >= MetadataLen + scion.MetaLen
//@ preserves forall i int :: 0 <= i && i < len(b) ==>
//@   acc(&b[i])
//@ ensures r == nil ==> p.Mem()
//@ ensures r != nil ==> p.NonInitMem()
//@ decreases
func (p *Path) DecodeFromBytes(b []byte) (r error) {
	if len(b) < MetadataLen {
		return serrors.New("EPIC Path raw too short", "expected", MetadataLen, "actual", len(b))
	}
	//@ assert MetadataLen == PktIDLen + HVFLen + HVFLen
	//@ unfold p.NonInitMem()
	//@ assert len(b[:PktIDLen]) >= PktIDLen
	//@ assert forall i int :: 0 <= i && i < PktIDLen ==>
	//@   &b[:PktIDLen][i] == &b[i]
	p.PktID.DecodeFromBytes(b[:PktIDLen])
	p.PHVF = make([]byte, HVFLen)
	p.LHVF = make([]byte, HVFLen)

	//@ preserves acc(p.PHVF)
	//@ preserves forall i int :: 0 <= i && i < HVFLen ==>
	//@   (acc(&b[PktIDLen + i], definitions.ReadL1) &&
	//@   &b[PktIDLen:(PktIDLen + HVFLen)][i] == &b[PktIDLen + i])
	//@ decreases
	//@ outline(
	copy(p.PHVF, b[PktIDLen:(PktIDLen+HVFLen)] /*@, definitions.ReadL1 @*/)
	//@ )

	//@ preserves acc(p.LHVF)
	//@ preserves len(b[(PktIDLen+HVFLen):MetadataLen]) == HVFLen
	//@ preserves forall i int :: 0 <= i && i < HVFLen ==>
	//@   (acc(&b[PktIDLen + HVFLen + i], definitions.ReadL1) &&
	//@   &b[(PktIDLen+HVFLen):MetadataLen][i] == &b[PktIDLen + HVFLen + i])
	//@ decreases
	//@ outline(
	copy(p.LHVF, b[(PktIDLen+HVFLen):MetadataLen] /*@, definitions.ReadL1 @*/)
	//@ )

	p.ScionPath = &scion.Raw{}
	//@ fold p.ScionPath.Base.NonInitMem()
	//@ fold p.ScionPath.NonInitMem()
	//@ assert len(b[MetadataLen:]) >= scion.MetaLen
	//@ assert len(b) - MetadataLen >= scion.MetaLen
	//@ assert forall i int :: 0 <= i && i < len(b) - MetadataLen ==>
	//@   &b[MetadataLen:][i] == &b[MetadataLen + i]
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
		return nil, err
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
//@ ensures 0 <= l
//@ decreases
func (p *Path) Len() (l int) {
	if p.ScionPath == nil {
		return /*@ unfolding acc(p.Mem(), _) in @*/ MetadataLen
	}
	return MetadataLen + p.ScionPath.Len()
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
//@ preserves forall i int :: 0 <= i && i < len(raw) ==>
//@   acc(&raw[i], definitions.ReadL1)
//@ ensures 0 <= i.Timestamp
//@ ensures 0 <= i.Counter
//@ decreases
func (i *PktID) DecodeFromBytes(raw []byte) {
	//@ assert forall i int :: 0 <= i && i < 4 ==>
	//@   &raw[:4][i] == &raw[i]
	i.Timestamp = binary.BigEndian.Uint32(raw[:4])
	//@ assert forall i int :: 0 <= i && i < 4 ==>
	//@   &raw[4:8][i] == &raw[4 + i]
	i.Counter = binary.BigEndian.Uint32(raw[4:8])
	//@ assume i.Timestamp >= 0
	//@ assume i.Counter >= 0
}

// SerializeTo serializes the PktID into the buffer (b).
//@ requires  len(b) >= PktIDLen
//@ preserves acc(i, definitions.ReadL1)
//@ preserves forall j int :: 0 <= j && j < len(b) ==>
//@   acc(&b[j])
//@ decreases
func (i *PktID) SerializeTo(b []byte) {
	//@ assert forall j int :: 0 <= 4 ==>
	//@   &b[:4][j] == &b[j]
	binary.BigEndian.PutUint32(b[:4], i.Timestamp)
	//@ assert forall j int :: 0 <= 4 ==>
	//@   &b[4:8][j] == &b[4 + j]
	binary.BigEndian.PutUint32(b[4:8], i.Counter)
}
