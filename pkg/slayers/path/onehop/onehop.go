// Copyright 2020 Anapaya Systems
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

package onehop

import (
	"github.com/scionproto/scion/pkg/private/serrors"
	"github.com/scionproto/scion/pkg/slayers/path"
	"github.com/scionproto/scion/pkg/slayers/path/scion"
	//@ "github.com/scionproto/scion/verification/utils/definitions"
	//@ "github.com/scionproto/scion/verification/utils/slices"
)

// PathLen is the length of a serialized one hop path in bytes.
const PathLen = path.InfoLen + 2*path.HopLen

const PathType path.Type = 2

//@ requires path.PathPackageMem()
//@ requires !path.Registered(PathType)
//@ ensures  path.PathPackageMem()
//@ ensures  forall t path.Type :: 0 <= t && t < path.MaxPathType ==>
//@ 	t != PathType ==> old(path.Registered(t)) == path.Registered(t)
//@ ensures  path.Registered(PathType)
//@ decreases
func RegisterPath() {
	tmp := path.Metadata{
		Type: PathType,
		Desc: "OneHop",
		New:
		//@ ensures p.NonInitMem()
		//@ ensures p != nil
		//@ decreases
		func /*@ newPath @*/ () (p path.Path) {
			onehopTmp := &Path{}
			//@ fold onehopTmp.NonInitMem()
			return onehopTmp
		},
	}
	/*@
	proof tmp.New implements path.NewPathSpec {
		return tmp.New() as newPath
	}
	@*/
	path.RegisterPath(tmp)
}

// Path encodes a one hop path. A one hop path is a special path that is created by a SCION router
// in the first AS and completed by a SCION router in the second AS. It is used during beaconing
// when there is not yet any other path segment available.
type Path struct {
	Info      path.InfoField
	FirstHop  path.HopField
	SecondHop path.HopField
}

//@ requires o.NonInitMem()
//@ requires 0 <= dataLen && dataLen <= len(underlyingBuf)
//@ requires len(data) == dataLen
//@ requires data === underlyingBuf[:dataLen]
//@ requires slices.AbsSlice_Bytes(underlyingBuf, 0, len(underlyingBuf))
//@ ensures  (len(data) >= PathLen) == (r == nil)
//@ ensures  r == nil ==> o.Mem()
//@ ensures  r == nil ==> o.GetUnderlyingBuf() === underlyingBuf
//@ ensures  r != nil ==> o.NonInitMem()
//@ ensures  r != nil ==> r.ErrorMem()
//@ ensures  r != nil ==> slices.AbsSlice_Bytes(underlyingBuf, 0, len(underlyingBuf))
//@ decreases
func (o *Path) DecodeFromBytes(data []byte /*@, underlyingBuf []byte, dataLen int @*/) (r error) {
	if len(data) < PathLen {
		return serrors.New("buffer too short for OneHop path", "expected", int(PathLen), "actual",
			int(len(data)))
	}
	offset := 0
	//@ unfold o.NonInitMem()
	//
	//@ ghost slices.SplitByIndex_Bytes(underlyingBuf, 0, len(underlyingBuf), dataLen, definitions.ReadL1)
	//@ ghost slices.Reslice_Bytes(underlyingBuf, 0, dataLen, definitions.ReadL1)
	//
	//@ ghost slices.SplitByIndex_Bytes(data, 0, len(data), path.InfoLen, definitions.ReadL1)
	//@ ghost slices.Reslice_Bytes(data, 0, path.InfoLen, definitions.ReadL1)
	if err := o.Info.DecodeFromBytes(data[:path.InfoLen]); err != nil {
		//@ ghost slices.Unslice_Bytes(data, 0, path.InfoLen, definitions.ReadL1)
		//@ ghost slices.CombineAtIndex_Bytes(data, 0, len(data), path.InfoLen, definitions.ReadL1)
		//@ ghost slices.Unslice_Bytes(underlyingBuf, 0, dataLen, definitions.ReadL1)
		//@ ghost slices.CombineAtIndex_Bytes(underlyingBuf, 0, len(underlyingBuf), dataLen, definitions.ReadL1)
		return err
	}
	//@ slices.Unslice_Bytes(data, 0, path.InfoLen, definitions.ReadL1)
	offset += path.InfoLen
	//@ assert acc(slices.AbsSlice_Bytes(data, 0, offset), definitions.ReadL1)
	//@ ghost slices.SplitByIndex_Bytes(data, offset, len(data), offset+path.HopLen, definitions.ReadL1)
	//@ ghost slices.Reslice_Bytes(data, offset, offset+path.HopLen, definitions.ReadL1)
	if err := o.FirstHop.DecodeFromBytes(data[offset : offset+path.HopLen]); err != nil {
		//@ ghost slices.Unslice_Bytes(data, offset, offset+path.HopLen, definitions.ReadL1)
		//@ ghost slices.CombineAtIndex_Bytes(data, offset, len(data), offset+path.HopLen, definitions.ReadL1)
		//@ ghost slices.CombineAtIndex_Bytes(data, 0, len(data), offset, definitions.ReadL1)
		//@ ghost slices.Unslice_Bytes(underlyingBuf, 0, dataLen, definitions.ReadL1)
		//@ ghost slices.CombineAtIndex_Bytes(underlyingBuf, 0, len(underlyingBuf), dataLen, definitions.ReadL1)
		return err
	}
	//@ ghost slices.Unslice_Bytes(data, offset, offset+path.HopLen, definitions.ReadL1)
	//@ ghost slices.CombineAtIndex_Bytes(data, 0, offset+path.HopLen, offset, definitions.ReadL1)
	offset += path.HopLen
	//@ ghost slices.SplitByIndex_Bytes(data, offset, len(data), offset+path.HopLen, definitions.ReadL1)
	//@ ghost slices.Reslice_Bytes(data, offset, offset+path.HopLen, definitions.ReadL1)
	r = o.SecondHop.DecodeFromBytes(data[offset : offset+path.HopLen])
	//@ ghost slices.Unslice_Bytes(data, offset, offset+path.HopLen, definitions.ReadL1)
	//@ ghost slices.CombineAtIndex_Bytes(data, offset, len(data), offset+path.HopLen, definitions.ReadL1)
	//@ ghost slices.CombineAtIndex_Bytes(data, 0, len(data), offset, definitions.ReadL1)
	//@ ghost slices.Unslice_Bytes(underlyingBuf, 0, dataLen, definitions.ReadL1)
	//@ ghost slices.CombineAtIndex_Bytes(underlyingBuf, 0, len(underlyingBuf), dataLen, definitions.ReadL1)
	//@ ghost if r == nil {
	//@   o.underlyingBuf = underlyingBuf
	//@   assert slices.AbsSlice_Bytes(o.underlyingBuf, 0, len(o.underlyingBuf))
	//@   fold o.Mem()
	//@ } else {
	//@   fold o.NonInitMem()
	//@ }
	return r
}

//@ preserves acc(o.Mem(), definitions.ReadL1)
//@ preserves underlyingBuf === o.GetUnderlyingBuf()
//@ preserves slices.AbsSlice_Bytes(b, 0, len(b))
//@ requires  0 <= dataLen && dataLen <= len(underlyingBuf)
//@ requires  len(b) == dataLen
//@ ensures   (len(b) >= PathLen) == (err == nil)
//@ ensures   err != nil ==> err.ErrorMem()
//@ decreases
func (o *Path) SerializeTo(b []byte /*@, underlyingBuf []byte, dataLen int @*/) (err error) {
	if len(b) < PathLen {
		return serrors.New("buffer too short for OneHop path", "expected", int(PathLen), "actual",
			int(len(b)))
	}
	offset := 0
	//@ unfold acc(o.Mem(), definitions.ReadL1)
	//@ ghost slices.SplitByIndex_Bytes(b, 0, len(b), path.InfoLen, writePerm)
	//@ ghost slices.Reslice_Bytes(b, 0, path.InfoLen, writePerm)
	if err := o.Info.SerializeTo(b[:offset+path.InfoLen]); err != nil {
		//@ ghost slices.Unslice_Bytes(b, 0, path.InfoLen, writePerm)
		//@ ghost slices.CombineAtIndex_Bytes(b, 0, len(b), path.InfoLen, writePerm)
		return err
	}
	//@ ghost slices.Unslice_Bytes(b, 0, path.InfoLen, writePerm)
	offset += path.InfoLen
	//@ ghost slices.SplitByIndex_Bytes(b, offset, len(b), offset+path.HopLen, writePerm)
	//@ ghost slices.Reslice_Bytes(b, offset, offset+path.HopLen, writePerm)
	if err := o.FirstHop.SerializeTo(b[offset : offset+path.HopLen]); err != nil {
		//@ ghost slices.Unslice_Bytes(b, offset, offset+path.HopLen, writePerm)
		//@ ghost slices.CombineAtIndex_Bytes(b, offset, len(b), offset+path.HopLen, writePerm)
		//@ ghost slices.CombineAtIndex_Bytes(b, 0, len(b), offset, writePerm)
		return err
	}
	//@ ghost slices.Unslice_Bytes(b, offset, offset+path.HopLen, writePerm)
	//@ ghost slices.CombineAtIndex_Bytes(b, 0, offset+path.HopLen, offset, writePerm)
	offset += path.HopLen
	//@ ghost slices.SplitByIndex_Bytes(b, offset, len(b), offset+path.HopLen, writePerm)
	//@ ghost slices.Reslice_Bytes(b, offset, offset+path.HopLen, writePerm)
	err = o.SecondHop.SerializeTo(b[offset : offset+path.HopLen])
	//@ ghost slices.Unslice_Bytes(b, offset, offset+path.HopLen, writePerm)
	//@ ghost slices.CombineAtIndex_Bytes(b, offset, len(b), offset+path.HopLen, writePerm)
	//@ ghost slices.CombineAtIndex_Bytes(b, 0, len(b), offset, writePerm)
	//@ fold acc(o.Mem(), definitions.ReadL1)
	return err
}

// ToSCIONDecoded converts the one hop path in to a normal SCION path in the
// decoded format.
//@ trusted // (VerifiedSCION) Currently takes a long time to verify
//@ requires o.Mem()
//@ ensures  err == nil ==> (sd != nil && sd.Mem())
//@ ensures  err == nil ==> sd.GetUnderlyingBuf() === old(o.GetUnderlyingBuf())
//@ ensures  err != nil ==> err.ErrorMem() && o.Mem()
//@ decreases
func (o *Path) ToSCIONDecoded() (sd *scion.Decoded, err error) {
	//@ unfold acc(o.Mem(), definitions.ReadL1)
	//@ unfold acc(o.SecondHop.Mem(), definitions.ReadL10)
	if o.SecondHop.ConsIngress == 0 {
		//@ fold acc(o.SecondHop.Mem(), definitions.ReadL10)
		//@ fold acc(o.Mem(), definitions.ReadL1)
		return nil, serrors.New("incomplete path can't be converted")
	}
	//@ fold acc(o.SecondHop.Mem(), definitions.ReadL10)
	p := &scion.Decoded{
		Base: scion.Base{
			PathMeta: scion.MetaHdr{
				SegLen: [3]uint8{2, 0, 0},
			},
			NumHops: 2,
			NumINF:  1,
		},
		InfoFields: []path.InfoField{
			{
				ConsDir:   true,
				SegID:     o.Info.SegID,
				Timestamp: o.Info.Timestamp,
			},
		},
		HopFields: []path.HopField{
			{
				IngressRouterAlert: o.FirstHop.IngressRouterAlert,
				EgressRouterAlert:  o.FirstHop.EgressRouterAlert,
				ConsIngress:        o.FirstHop.ConsIngress,
				ConsEgress:         o.FirstHop.ConsEgress,
				ExpTime:            o.FirstHop.ExpTime,
				Mac:                o.FirstHop.Mac,
			},
			{
				IngressRouterAlert: o.SecondHop.IngressRouterAlert,
				EgressRouterAlert:  o.SecondHop.EgressRouterAlert,
				ConsIngress:        o.SecondHop.ConsIngress,
				ConsEgress:         o.SecondHop.ConsEgress,
				ExpTime:            o.SecondHop.ExpTime,
				Mac:                o.SecondHop.Mac,
			},
		},
	}
	// (VerifiedSCION) this verification times out. Even folding
	// the base predicate and assuming false for the rest takes a
	// significant amount of time.
	//@ fold p.Base.Mem()
	//@ fold p.HopFields[0].Mem()
	//@ fold p.HopFields[1].Mem()
	//@ unfold acc(o.Mem(), definitions.ReadL1)
	//@ p.underlyingBuf = o.underlyingBuf
	//@ fold p.Mem()
	return p, nil
}

// Reverse a OneHop path that returns a reversed SCION path.
//@ requires o.Mem()
//@ ensures err == nil ==> p != nil
//@ ensures err == nil ==> p.Mem()
//@ ensures err == nil ==> p.GetUnderlyingBuf() === old(o.GetUnderlyingBuf())
//@ ensures err == nil ==> typeOf(p) == type[*scion.Decoded]
//@ ensures err != nil ==> err.ErrorMem()
//@ decreases
func (o *Path) Reverse() (p path.Path, err error) {
	sp, err := o.ToSCIONDecoded()
	if err != nil {
		return nil, serrors.WrapStr("converting to scion path", err)
	}
	// increment the path, since we are at the receiver side.
	if err := sp.IncPath(); err != nil {
		return nil, serrors.WrapStr("incrementing path", err)
	}
	return sp.Reverse()
}

//@ pure
//@ ensures l == PathLen
//@ decreases
func (o *Path) Len() (l int) {
	return PathLen
}

//@ pure
//@ ensures t == PathType
//@ decreases
func (o *Path) Type() (t path.Type) {
	return PathType
}
