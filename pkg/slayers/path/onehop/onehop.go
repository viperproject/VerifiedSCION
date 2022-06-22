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
)

// PathLen is the length of a serialized one hop path in bytes.
const PathLen = path.InfoLen + 2*path.HopLen

const PathType path.Type = 2

// func RegisterPath() {
// 	path.RegisterPath(path.Metadata{
// 		Type: PathType,
// 		Desc: "OneHop",
// 		New: func() path.Path {
// 			return &Path{}
// 		},
// 	})
// }

// Path encodes a one hop path. A one hop path is a special path that is created by a SCION router
// in the first AS and completed by a SCION router in the second AS. It is used during beaconing
// when there is not yet any other path segment available.
type Path struct {
	Info      path.InfoField
	FirstHop  path.HopField
	SecondHop path.HopField
}

//@ requires o.NonInitMem()
//@ requires len(data) >= PathLen
//@ preserves forall i int :: 0 <= i && i < len(data) ==>
//@     acc(&data[i], definitions.ReadL1)
//@ ensures r != nil ==> (o.NonInitMem() && r.ErrorMem())
//@ ensures r == nil ==> o.Mem()
//@ decreases
func (o *Path) DecodeFromBytes(data []byte) (r error) {
	if len(data) < PathLen {
		return serrors.New("buffer too short for OneHop path", "expected", PathLen, "actual",
			len(data))
	}
	offset := 0
	//@ unfold o.NonInitMem()
	if err := o.Info.DecodeFromBytes(data[:path.InfoLen]); err != nil {
		return err
	}
	offset += path.InfoLen
	//@ assert 0 <= offset && offset + path.HopLen <= len(data)
	//@ assert forall i int :: 0 <= i && i < path.HopLen ==>
	//@     &data[offset : offset+path.HopLen][i] == &data[offset + i]
	if err := o.FirstHop.DecodeFromBytes(data[offset : offset+path.HopLen]); err != nil {
		return err
	}
	offset += path.HopLen
	//@ assert 0 <= offset && offset + path.HopLen <= len(data)
	//@ assert forall i int :: 0 <= i && i < path.HopLen ==>
	//@     &data[offset : offset+path.HopLen][i] == &data[offset + i]
	r = o.SecondHop.DecodeFromBytes(data[offset : offset+path.HopLen])
	//@ ghost if r == nil {
	//@     fold o.Mem()
  //@ }
	return r
}

//@ requires len(b) >= PathLen
//@ preserves acc(o.Mem(), definitions.ReadL1)
//@ preserves forall i int :: 0 <= i && i < len(b) ==>
//@     acc(&b[i])
//@ ensures err == nil
//@ decreases
func (o *Path) SerializeTo(b []byte) (err error) {
	if len(b) < PathLen {
		return serrors.New("buffer too short for OneHop path", "expected", PathLen, "actual",
			len(b))
	}
	offset := 0
	//@ unfold acc(o.Mem(), definitions.ReadL1)
	if err := o.Info.SerializeTo(b[:offset+path.InfoLen]); err != nil {
		return err
	}
	offset += path.InfoLen
	//@ assert 0 <= offset && offset + path.HopLen <= len(b)
	//@ assert forall i int :: 0 <= i && i < path.HopLen ==>
	//@     &b[offset : offset+path.HopLen][i] == &b[offset + i]
	if err := o.FirstHop.SerializeTo(b[offset : offset+path.HopLen]); err != nil {
		return err
	}
	offset += path.HopLen
	//@ assert 0 <= offset && offset + path.HopLen <= len(b)
	//@ assert forall i int :: 0 <= i && i < path.HopLen ==>
	//@     &b[offset : offset+path.HopLen][i] == &b[offset + i]
	err = o.SecondHop.SerializeTo(b[offset : offset+path.HopLen])
	//@ ghost if err == nil {
	//@   fold acc(o.Mem(), definitions.ReadL1)
  //@ }
	return err
}

// ToSCIONDecoded converts the one hop path in to a normal SCION path in the
// decoded format.
// func (o *Path) ToSCIONDecoded() (sd *scion.Decoded, err error) {
// 	if o.SecondHop.ConsIngress == 0 {
// 		return nil, serrors.New("incomplete path can't be converted")
// 	}
// 	p := &scion.Decoded{
// 		Base: scion.Base{
// 			PathMeta: scion.MetaHdr{
// 				SegLen: [3]uint8{2, 0, 0},
// 			},
// 			NumHops: 2,
// 			NumINF:  1,
// 		},
// 		InfoFields: []path.InfoField{
// 			{
// 				ConsDir:   true,
// 				SegID:     o.Info.SegID,
// 				Timestamp: o.Info.Timestamp,
// 			},
// 		},
// 		HopFields: []path.HopField{
// 			{
// 				IngressRouterAlert: o.FirstHop.IngressRouterAlert,
// 				EgressRouterAlert:  o.FirstHop.EgressRouterAlert,
// 				ConsIngress:        o.FirstHop.ConsIngress,
// 				ConsEgress:         o.FirstHop.ConsEgress,
// 				ExpTime:            o.FirstHop.ExpTime,
// 				Mac:                o.FirstHop.Mac,
// 			},
// 			{
// 				IngressRouterAlert: o.SecondHop.IngressRouterAlert,
// 				EgressRouterAlert:  o.SecondHop.EgressRouterAlert,
// 				ConsIngress:        o.SecondHop.ConsIngress,
// 				ConsEgress:         o.SecondHop.ConsEgress,
// 				ExpTime:            o.SecondHop.ExpTime,
// 				Mac:                o.SecondHop.Mac,
// 			},
// 		},
// 	}
// 	return p, nil
// }

// Reverse a OneHop path that returns a reversed SCION path.
// func (o Path) Reverse() (p path.Path, err error) {
// 	sp, err := o.ToSCIONDecoded()
// 	if err != nil {
// 		return nil, serrors.WrapStr("converting to scion path", err)
// 	}
// 	// increment the path, since we are at the receiver side.
// 	if err := sp.IncPath(); err != nil {
// 		return nil, serrors.WrapStr("incrementing path", err)
// 	}
// 	return sp.Reverse()
// }

//@ pure
//@ ensures 0 <= l
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
