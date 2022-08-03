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
)

// PathLen is the length of a serialized empty path in bytes.
const PathLen = 0

const PathType path.Type = 0

/*
func RegisterPath() {
	path.RegisterPath(path.Metadata{
		Type: PathType,
		Desc: "Empty",
		New: func() path.Path {
			return Path{}
		},
	})
}
*/

// Path encodes an empty path. An empty path is a special path that takes zero
// bytes on the wire and is used for AS internal communication.
type Path struct{}

//@ ensures len(r) != 0 ==> (e != nil && e.ErrorMem())
//@ ensures len(r) == 0 ==> e == nil
//@ ensures o.Mem()
//@ decreases
func (o Path) DecodeFromBytes(r []byte) (e error) {
	//@ fold o.Mem()
	if len(r) != 0 {
		// TODO: undo the cast done bellow, should not be required according to the spec of definitions.IsPrimitiveType
		return serrors.New("decoding an empty path", "len", int(len(r)))
	}
	return nil
}

//@ ensures e == nil
//@ decreases
func (o Path) SerializeTo(b []byte) (e error) {
	return nil
}

//@ ensures p == o
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
