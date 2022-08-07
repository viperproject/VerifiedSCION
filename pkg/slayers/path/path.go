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

//@ initEnsures PathPackageMem(true)
package path

import (
	"fmt"

	"github.com/scionproto/scion/pkg/private/serrors"
	//@ "github.com/scionproto/scion/verification/utils/definitions"
	//@ "github.com/scionproto/scion/verification/utils/slices"
)

// PathType is uint8 so 256 values max.
const maxPathType = 256

var (
	registeredPaths [maxPathType]metadata
	strictDecoding  bool = true
)

// Ghost initialization code to establish the PathPackageMem predicate.
/*@
func init() {
	assert acc(&registeredPaths)
	assert acc(&strictDecoding)
	assert strictDecoding
	fold PathPackageMem(true)
}
@*/

// Type indicates the type of the path contained in the SCION header.
type Type uint8

//@ requires 0 <= t && t < maxPathType
//@ preserves acc(PathPackageMem(b), definitions.ReadL20)
//@ decreases
func (t Type) String( /*@ ghost b bool @*/ ) string {
	//@ unfold acc(PathPackageMem(b), definitions.ReadL20)
	//@ ghost defer fold acc(PathPackageMem(b), definitions.ReadL20)
	pm := registeredPaths[t]
	if !pm.inUse {
		return fmt.Sprintf("UNKNOWN (%d)", int(t))
	}
	return fmt.Sprintf("%v (%d)", pm.Desc, t)
}

// Path is the path contained in the SCION header.
type Path interface {
	// (VerifiedSCION) Must hold in every valid of Path.
	//@ pred Mem()
	// (VerifiedSCION) Must imply the resources required to initialize
	// a new instance of a predicate.
	//@ pred NonInitMem()
	// SerializeTo serializes the path into the provided buffer.
	// (VerifiedSCION) There are implementations of this interface that modify the underlying
	// structure when serializing (e.g. scion.Raw)
	//@ preserves Mem()
	//@ preserves slices.AbsSlice_Bytes(b, 0, len(b))
	//@ ensures   e != nil ==> e.ErrorMem()
	//@ decreases
	SerializeTo(b []byte) (e error)
	// DecodesFromBytes decodes the path from the provided buffer.
	// (VerifiedSCION) There are implementations of this interface (e.g. scion.Raw) that
	// store b and use it as internal data.
	//@ requires NonInitMem()
	//@ requires slices.AbsSlice_Bytes(b, 0, len(b))
	//@ ensures  err == nil ==> Mem()
	//@ ensures  err != nil ==> err.ErrorMem()
	//@ decreases
	DecodeFromBytes(b []byte) (err error)
	// Reverse reverses a path such that it can be used in the reversed direction.
	//
	// XXX(shitz): This method should possibly be moved to a higher-level path manipulation package.
	//@ requires Mem()
	//@ ensures  e == nil ==> p.Mem()
	//@ ensures  e == nil ==> p != nil
	//@ ensures  e != nil ==> e.ErrorMem()
	//@ decreases
	Reverse() (p Path, e error)
	// Len returns the length of a path in bytes.
	//@ pure
	//@ requires acc(Mem(), _)
	//  ensures  l >= 0 // TODO: open issue, this causes exception
	//@ decreases
	Len() (l int)
	// Type returns the type of a path.
	//@ pure
	//@ requires acc(Mem(), _)
	//@ decreases
	Type() Type
	//@ ghost
	//@ requires Mem()
	//@ ensures  NonInitMem()
	//@ decreases
	//@ DowngradePerm()
}

type metadata struct {
	inUse bool
	Metadata
}

// Metadata defines a new SCION path type, used for dynamic SICON path type registration.
type Metadata struct {
	// Type is a unique value for the path.
	Type Type
	// Desc is the description/name of the path.
	Desc string
	// New is a path constructor function.
	New func() Path
}

// RegisterPath registers a new SCION path type globally.
// The PathType passed in must be unique, or a runtime panic will occur.
//@ requires 0 <= pathMeta.Type && pathMeta.Type < maxPathType
//@ requires PathPackageMem(current)
//@ requires !Registered(pathMeta.Type, current)
//@ ensures  PathPackageMem(current)
//@ ensures  forall t Type :: 0 <= t && t < maxPathType ==>
//@ 	t != pathMeta.Type ==> old(Registered(t, current)) == Registered(t, current)
//@ ensures  Registered(pathMeta.Type, current)
//@ decreases
func RegisterPath(pathMeta Metadata /*@ , ghost current bool @*/) {
	//@ unfold PathPackageMem(current)
	pm := registeredPaths[pathMeta.Type]
	if pm.inUse {
		panic("path type already registered")
	}
	registeredPaths[pathMeta.Type].inUse = true
	registeredPaths[pathMeta.Type].Metadata = pathMeta
	//@ fold PathPackageMem(current)
}

// StrictDecoding enables or disables strict path decoding. If enabled, unknown
// path types fail to decode. If disabled, unknown path types are decoded into a
// raw path that keeps the encoded path around for re-serialization.
//
// Strict parsing is enabled by default.
//
// Experimental: This function is experimental and might be subject to change.
//@ requires PathPackageMem(current)
//@ ensures  PathPackageMem(strict)
//@ decreases
func StrictDecoding(strict bool /*@ , ghost current bool @*/) {
	//@ unfold PathPackageMem(current)
	strictDecoding = strict
	//@ fold PathPackageMem(strict)
}

/* TODO:
// NewPath returns a new path object of pathType.
func NewPath(pathType Type) (Path, error) {
	pm := registeredPaths[pathType]
	if !pm.inUse {
		if strictDecoding {
			return nil, serrors.New("unsupported path", "type", pathType)
		}
		return &rawPath{}, nil
	}
	return pm.New(), nil
}
*/

// NewRawPath returns a new raw path that can hold any path type.
func NewRawPath() Path {
	return &rawPath{}
}

type rawPath struct {
	raw      []byte
	pathType Type
}

//@ preserves acc(p.Mem(), definitions.ReadL10)
//@ preserves slices.AbsSlice_Bytes(b, 0, len(b))
//@ ensures   e == nil
//@ decreases
func (p *rawPath) SerializeTo(b []byte) (e error) {
	//@ unfold slices.AbsSlice_Bytes(b, 0, len(b))
	//@ unfold acc(p.Mem(), definitions.ReadL10)
	//@ unfold acc(slices.AbsSlice_Bytes(p.raw, 0, len(p.raw)), definitions.ReadL11)
	copy(b, p.raw /*@, definitions.ReadL11 @*/)
	//@ fold acc(slices.AbsSlice_Bytes(p.raw, 0, len(p.raw)), definitions.ReadL11)
	//@ fold acc(p.Mem(), definitions.ReadL10)
	//@ fold slices.AbsSlice_Bytes(b, 0, len(b))
	return nil
}

//@ requires p.NonInitMem() && slices.AbsSlice_Bytes(b, 0, len(b))
//@ ensures  p.Mem()
//@ ensures  e == nil
//@ decreases
func (p *rawPath) DecodeFromBytes(b []byte) (e error) {
	//@ unfold p.NonInitMem()
	p.raw = b
	//@ fold p.Mem()
	return nil
}

//@ requires p.Mem()
//@ ensures  e != nil && e.ErrorMem()
//@ decreases
func (p *rawPath) Reverse() (r Path, e error) {
	return nil, serrors.New("not supported")
}

//@ pure
//@ requires acc(p.Mem(), _)
//@ ensures l >= 0
//@ decreases
func (p *rawPath) Len() (l int) {
	return /*@ unfolding acc(p.Mem(), _) in @*/ len(p.raw)
}

//@ pure
//@ requires acc(p.Mem(), _)
//@ decreases
func (p *rawPath) Type() Type {
	return /*@ unfolding acc(p.Mem(), _) in @*/ p.pathType
}
