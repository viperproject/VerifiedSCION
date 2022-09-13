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

package empty

import (
	"github.com/scionproto/scion/pkg/private/serrors"
	"github.com/scionproto/scion/pkg/slayers/path"
	//@ "github.com/scionproto/scion/verification/utils/slices"
)

// PathLen is the length of a serialized empty path in bytes.
const PathLen = 0

const PathType path.Type = 0

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
		Desc: "Empty",
		New:
		//@ ensures p.NonInitMem()
		//@ decreases
		func /*@ newPath @*/ () (p path.Path) {
			emptyTmp /*@@@*/ := Path{}
			//@ fold emptyTmp.NonInitMem()
			return emptyTmp
		},
	}
	/*@
	proof tmp.New implements path.NewPathSpec {
		return tmp.New() as newPath
	}
	@*/
	path.RegisterPath(tmp)
}

// Path encodes an empty path. An empty path is a special path that takes zero
// bytes on the wire and is used for AS internal communication.
type Path struct {
	//@ underlyingBuf []byte
}

//@ requires len(r) == dataLen
//@ requires slices.AbsSlice_Bytes(underlyingBuf, 0, len(underlyingBuf))
//@ ensures  dataLen == 0 ==> e == nil
//@ ensures  dataLen == 0 ==> o.Mem()
//@ ensures  dataLen == 0 ==> underlyingBuf === o.GetUnderlyingBuf()
//@ ensures  dataLen != 0 ==> e != nil
//@ ensures  dataLen != 0 ==> e.ErrorMem()
//@ ensures  dataLen != 0 ==> o.NonInitMem()
//@ ensures  dataLen != 0 ==> slices.AbsSlice_Bytes(underlyingBuf, 0, len(underlyingBuf))
//@ decreases
func (o Path) DecodeFromBytes(r []byte /*@, underlyingBuf []byte, dataLen int @*/) (e error) {
	if len(r) != 0 {
		//@ fold o.NonInitMem()
		// (VerifiedSCION) TODO: undo the cast done bellow, should not be required according to the spec of definitions.IsPrimitiveType
		//@ assert dataLen != 0
		return serrors.New("decoding an empty path", "len", int(len(r)))
	}
	//@ assert dataLen == 0
	//@ o.underlyingBuf = underlyingBuf
	//@ fold o.Mem()
	//@ assert o.Mem()
	//
	// TODO FIXME ask Joao, probably something with value
	// receiver you aren't understanding
	//@ assume false
	return nil
}

//@ ensures e == nil
//@ decreases
func (o Path) SerializeTo(b []byte /*@, underlyingBuf []byte, dataLen int @*/) (e error) {
	return nil
}

//@ ensures p === o
//@ ensures e == nil
//@ decreases
func (o Path) Reverse() (p path.Path, e error) {
	return o, nil
}

//@ pure
//@ ensures r >= 0
//@ decreases
func (o Path) Len() (r int) {
	return PathLen
}

//@ pure
//@ ensures r == PathType
//@ decreases
func (o Path) Type() (r path.Type) {
	return PathType
}
