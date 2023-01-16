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

package slayers

import (
	"fmt"

	"github.com/google/gopacket"

	"github.com/scionproto/scion/pkg/private/serrors"
	// @ def "github.com/scionproto/scion/verification/utils/definitions"
	// @ sl  "github.com/scionproto/scion/verification/utils/slices"
)

var (
	ErrOptionNotFound = serrors.New("Option not found")
)

// OptionType indicates the type of a TLV Option that is part of an extension header.
type OptionType uint8

// Definition of option type constants.
const (
	OptTypePad1 OptionType = iota
	OptTypePadN
	OptTypeAuthenticator
)

type tlvOption struct {
	OptType      OptionType
	OptDataLen   uint8
	ActualLength int
	OptData      []byte
	OptAlign     [2]uint8 // Xn+Y = [2]uint8{X, Y}
}

// @ preserves acc(o, def.ReadL20)
// @ ensures   0 < res
// @ ensures   o.OptType == OptTypePad1 ==> res == 1
// @ ensures   o.OptType != OptTypePad1 ==> 2 <= res
// @ ensures   fixLengths  && o.OptType != OptTypePad1 ==> res == len(o.OptData) + 2
// @ ensures   !fixLengths && o.OptType != OptTypePad1 ==> res == int(o.OptDataLen) + 2
// (VerifiedSCION): maybe drop the following postcondition:
// ensures   res == o.lengthGhost(fixLengths)
// @ decreases
func (o *tlvOption) length(fixLengths bool) (res int) {
	if o.OptType == OptTypePad1 {
		return 1
	}
	if fixLengths {
		return len(o.OptData) + 2
	}
	// (VerifiedSCION) gobra cannot prove this yet, even though it must hold
	//                 as the type of o.OptDataLen is uint8
	// @ assume 0 <= o.OptDataLen
	return int(o.OptDataLen) + 2
}

// @ requires  2 <= len(data)
// @ preserves acc(o)
// @ preserves acc(sl.AbsSlice_Bytes(o.OptData, 0, len(o.OptData)), def.ReadL20)
// @ preserves sl.AbsSlice_Bytes(data, 0, len(data))
// @ decreases
func (o *tlvOption) serializeTo(data []byte, fixLengths bool) {
	dryrun := data == nil
	if o.OptType == OptTypePad1 {
		if !dryrun {
			// @ unfold sl.AbsSlice_Bytes(data, 0, len(data))
			data[0] = 0x0
			// @ fold sl.AbsSlice_Bytes(data, 0, len(data))
		}
		return
	}
	if fixLengths {
		o.OptDataLen = uint8(len(o.OptData))
	}
	if !dryrun {
		// @ unfold sl.AbsSlice_Bytes(data, 0, len(data))
		// @ unfold acc(sl.AbsSlice_Bytes(o.OptData, 0, len(o.OptData)), def.ReadL20)
		data[0] = uint8(o.OptType)
		data[1] = o.OptDataLen
		// @ assert forall i int :: { &data[2:][i] } 0 <= i && i < len(data[2:]) ==> &data[2:][i] == &data[2+i]
		copy(data[2:], o.OptData /*@ , def.ReadL20 @*/)
		// @ fold acc(sl.AbsSlice_Bytes(o.OptData, 0, len(o.OptData)), def.ReadL20)
		// @ fold sl.AbsSlice_Bytes(data, 0, len(data))
	}
}

// @ requires  2 <= len(data)
// @ preserves acc(sl.AbsSlice_Bytes(data, 0, len(data)), def.ReadL20)
// @ ensures   err == nil ==> acc(res)
// @ ensures   (err == nil && res.OptType != OptTypePad1) ==> (
// @ 	2 <= res.ActualLength && res.ActualLength <= len(data) && res.OptData === data[2:res.ActualLength])
// @ ensures   err != nil ==> err.ErrorMem()
// @ decreases
func decodeTLVOption(data []byte) (res *tlvOption, err error) {
	// @ unfold acc(sl.AbsSlice_Bytes(data, 0, len(data)), def.ReadL20)
	// @ defer fold acc(sl.AbsSlice_Bytes(data, 0, len(data)), def.ReadL20)
	o := &tlvOption{OptType: OptionType(data[0])}
	if OptionType(data[0]) == OptTypePad1 {
		o.ActualLength = 1
		return o, nil
	}
	if len(data) < 2 {
		return nil, serrors.New("buffer too short", "expected", 2, "actual", len(data))
	}
	o.OptDataLen = data[1]
	// (VerifiedSCION) Gobra cannot prove this even though it must hold, given the type of o.OptDataLen
	// @ assume 0 <= o.OptDataLen
	o.ActualLength = int(o.OptDataLen) + 2
	if len(data) < o.ActualLength {
		return nil, serrors.New("buffer too short", "expected", o.ActualLength, "actual", len(data))
	}
	// @ assert forall i int :: { &data[2:o.ActualLength][i] } 0 <= i && i < len(data[2:o.ActualLength]) ==>
	// @ 	&data[2:o.ActualLength][i] == &data[2+i]
	o.OptData = data[2:o.ActualLength]
	return o, nil
}

// serializeTLVOptionPadding adds an appropriate PadN extension.
// @ requires  padLength == 1 ==> 1 <= len(data)
// @ requires  1 < padLength  ==> 2 <= len(data)
// @ preserves sl.AbsSlice_Bytes(data, 0, len(data))
// @ decreases
func serializeTLVOptionPadding(data []byte, padLength int) {
	if padLength <= 0 {
		return
	}
	if padLength == 1 {
		// @ unfold sl.AbsSlice_Bytes(data, 0, len(data))
		data[0] = 0x0
		// @ fold sl.AbsSlice_Bytes(data, 0, len(data))
		return
	}
	dataLen := uint8(padLength) - 2
	padN /*@@@*/ := tlvOption{
		OptType:    OptTypePadN,
		OptDataLen: dataLen,
		OptData:    make([]byte, int(dataLen)),
	}
	// @ fold sl.AbsSlice_Bytes(padN.OptData, 0, len(padN.OptData))
	padN.serializeTo(data, false)
}

// serializeTLVOptions serializes options to buf and returns the length of the serialized options.
// Passing in a nil-buffer will treat the serialization as a dryrun that can be used to calculate
// the length needed for the buffer.
// (VerifiedSCION) Serialization of extensions is never invoked in the router.
// @ requires false
func serializeTLVOptions(buf []byte, options []*tlvOption, fixLengths bool) (res int) {
	dryrun := buf == nil
	// length start at 2 since the padding needs to be calculated taking the first 2 bytes of the
	// extension header (NextHdr and ExtLen fields) into account.
	length := 2
	for _, opt := range options /*@ with i0 @*/ {
		if fixLengths {
			x := int(opt.OptAlign[0])
			y := int(opt.OptAlign[1])
			if x != 0 {
				n := length / x
				offset := x*n + y
				if offset < length {
					offset += x
				}
				if length != offset {
					pad := offset - length
					if !dryrun {
						serializeTLVOptionPadding(buf[length-2:], pad)
					}
					length += pad
				}
			}
		}
		if !dryrun {
			opt.serializeTo(buf[length-2:], fixLengths)
		}
		length += opt.length(fixLengths)
	}
	if fixLengths {
		p := length % LineLen
		if p != 0 {
			pad := LineLen - p
			if !dryrun {
				serializeTLVOptionPadding(buf[length-2:], pad)
			}
			length += pad
		}
	}
	return length - 2
}

type extnBase struct {
	BaseLayer
	NextHdr L4ProtocolType
	// ExtLen is the length of the extension header in multiple of 4-bytes NOT including the
	// first 4 bytes.
	ExtLen    uint8
	ActualLen int
}

// @ requires false
func (e *extnBase) serializeToWithTLVOptions(b gopacket.SerializeBuffer,
	opts gopacket.SerializeOptions, tlvOptions []*tlvOption) error {

	l := serializeTLVOptions(nil, tlvOptions, opts.FixLengths)
	// @ ghost var resPB1 []byte
	bytes, err /*@ , resPB1 @*/ := b.PrependBytes(l /*@, nil @*/)
	if err != nil {
		return err
	}
	serializeTLVOptions(bytes, tlvOptions, opts.FixLengths)

	length := len(bytes) + 2
	if length%LineLen != 0 {
		return serrors.New("SCION extension actual length must be multiple of 4")
	}
	// @ ghost var resPB2 []byte
	bytes, err /*@ , resPB2 @*/ = b.PrependBytes(2 /*@, nil @*/)
	if err != nil {
		return err
	}
	bytes[0] = uint8(e.NextHdr)
	if opts.FixLengths {
		e.ExtLen = uint8((length / LineLen) - 1)
	}
	bytes[1] = e.ExtLen
	return nil
}

// @ requires  sl.AbsSlice_Bytes(data, 0, len(data))
// @ requires  df != nil
// @ preserves df.Mem()
// @ ensures   resErr != nil ==> resErr.ErrorMem()
// @ ensures   sl.AbsSlice_Bytes(data, 0, len(data))
// The following poscondition is more a lot more complicated than it would be if the return type
// was *extnBase instead of extnBase
// @ ensures   resErr == nil ==> (
// @ 	0 <= res.ActualLen && res.ActualLen <= len(data) &&
// @ 	res.BaseLayer.Contents === data[:res.ActualLen] &&
// @ 	res.BaseLayer.Payload === data[res.ActualLen:])
// @ decreases
func decodeExtnBase(data []byte, df gopacket.DecodeFeedback) (res extnBase, resErr error) {
	e := extnBase{}
	if len(data) < 2 {
		df.SetTruncated()
		return e, serrors.New(fmt.Sprintf("invalid extension header. Length %d less than 2",
			len(data)))
	}

	// @ unfold sl.AbsSlice_Bytes(data, 0, len(data))
	e.NextHdr = L4ProtocolType(data[0])
	e.ExtLen = data[1]
	// @ fold sl.AbsSlice_Bytes(data, 0, len(data))
	e.ActualLen = (int(e.ExtLen) + 1) * LineLen
	if len(data) < e.ActualLen {
		return extnBase{}, serrors.New(fmt.Sprintf("invalid extension header. "+
			"Length %d less than specified length %d", len(data), e.ActualLen))
	}
	// (VerifiedSCION) assumed because of Gobra's limitations. Nonetheless, we should know from the the type
	// of e.ExtLen that this property always holds.
	// @ assume 0 <= e.ExtLen
	// @ assert 0 <= e.ActualLen
	e. /*@ BaseLayer. @*/ Contents = data[:e.ActualLen]
	e. /*@ BaseLayer. @*/ Payload = data[e.ActualLen:]
	return e, nil
}

// HopByHopOption is a TLV option present in a SCION hop-by-hop extension.
type HopByHopOption tlvOption

// HopByHopExtn is the SCION hop-by-hop options extension.
type HopByHopExtn struct {
	extnBase
	Options []*HopByHopOption
}

// @ pure
// @ decreases
func (h *HopByHopExtn) LayerType() gopacket.LayerType {
	return LayerTypeHopByHopExtn
}

// @ decreases
func (h *HopByHopExtn) CanDecode() gopacket.LayerClass {
	return LayerClassHopByHopExtn
}

// @ trusted
// @ preserves acc(h.Mem(ubuf), def.ReadL20)
// @ decreases
func (h *HopByHopExtn) NextLayerType( /*@ ghost ubuf []byte @*/ ) gopacket.LayerType {
	return scionNextLayerTypeAfterHBH(h.NextHdr)
}

// @ trusted
// @ requires h.Mem(ub)
// @ ensures  sl.AbsSlice_Bytes(res, 0, len(res))
// @ ensures  sl.AbsSlice_Bytes(res, 0, len(res)) --* h.Mem(ub)
// @ decreases
func (h *HopByHopExtn) LayerPayload( /*@ ghost ub []byte @*/ ) (res []byte) {
	return h.Payload
}

// SerializeTo implementation according to gopacket.SerializableLayer.
// (VerifiedSCION) Serialization of extensions is never invoked in the router.
// @ requires false
func (h *HopByHopExtn) SerializeTo(b gopacket.SerializeBuffer,
	opts gopacket.SerializeOptions) error {

	if err := checkHopByHopExtnNextHdr(h.NextHdr); err != nil {
		return err
	}

	o := make([]*tlvOption, 0, len(h.Options))
	for _, v := range h.Options {
		o = append( /*@ perm(0/1), @*/ o, (*tlvOption)(v))
	}

	return h.extnBase.serializeToWithTLVOptions(b, opts, o)
}

// DecodeFromBytes implementation according to gopacket.DecodingLayer.
// @ trusted
// @ requires  sl.AbsSlice_Bytes(data, 0, len(data))
// @ requires  h.NonInitMem()
// @ requires  df != nil
// @ preserves df.Mem()
// @ ensures   res == nil ==> h.Mem(data)
// @ ensures   res != nil ==> (h.NonInitMem() && res.ErrorMem())
// @ ensures   res != nil ==> sl.AbsSlice_Bytes(data, 0, len(data))
// @ decreases
func (h *HopByHopExtn) DecodeFromBytes(data []byte, df gopacket.DecodeFeedback) (res error) {
	var err error
	h.extnBase, err = decodeExtnBase(data, df)
	if err != nil {
		return err
	}
	if err := checkHopByHopExtnNextHdr(h.NextHdr); err != nil {
		return err
	}
	offset := 2
	for offset < h.ActualLen {
		opt, err := decodeTLVOption(data[offset:h.ActualLen])
		if err != nil {
			return err
		}
		h.Options = append(h.Options, (*HopByHopOption)(opt))
		offset += opt.ActualLength
	}
	return nil
}

// @ trusted
// @ requires false
func decodeHopByHopExtn(data []byte, p gopacket.PacketBuilder) error {
	h := &HopByHopExtn{}
	err := h.DecodeFromBytes(data, p)
	p.AddLayer(h)
	if err != nil {
		return err
	}
	return p.NextDecoder(scionNextLayerTypeAfterHBH(h.NextHdr))
}

// @ ensures (t == HopByHopClass) == (err != nil)
// @ ensures err != nil ==> err.ErrorMem()
// @ decreases
func checkHopByHopExtnNextHdr(t L4ProtocolType) (err error) {
	if t == HopByHopClass {
		return serrors.New("hbh extension must not be repeated")
	}
	return nil
}

// EndToEndOption is a TLV option present in a SCION end-to-end extension.
type EndToEndOption tlvOption

// EndToEndExtn is the SCION end-to-end options extension.
type EndToEndExtn struct {
	extnBase
	Options []*EndToEndOption
}

// @ pure
// @ decreases
func (e *EndToEndExtn) LayerType() gopacket.LayerType {
	return LayerTypeEndToEndExtn
}

// @ decreases
func (e *EndToEndExtn) CanDecode() gopacket.LayerClass {
	return LayerClassEndToEndExtn
}

// @ trusted
// @ preserves acc(e.Mem(ubuf), def.ReadL20)
// @ decreases
func (e *EndToEndExtn) NextLayerType( /*@ ghost ubuf []byte @*/ ) gopacket.LayerType {
	return scionNextLayerTypeAfterE2E(e.NextHdr)
}

// @ trusted
// @ requires e.Mem(ub)
// @ ensures  sl.AbsSlice_Bytes(res, 0, len(res))
// @ ensures  sl.AbsSlice_Bytes(res, 0, len(res)) --* e.Mem(ub)
// @ decreases
func (e *EndToEndExtn) LayerPayload( /*@ ghost ub []byte @*/ ) (res []byte) {
	return e.Payload
}

// DecodeFromBytes implementation according to gopacket.DecodingLayer.
// @ trusted
// @ requires  sl.AbsSlice_Bytes(data, 0, len(data))
// @ requires  e.NonInitMem()
// @ requires  df != nil
// @ preserves df.Mem()
// @ ensures   res == nil ==> e.Mem(data)
// @ ensures   res != nil ==> (e.NonInitMem() && res.ErrorMem())
// @ ensures   res != nil ==> sl.AbsSlice_Bytes(data, 0, len(data))
// @ decreases
func (e *EndToEndExtn) DecodeFromBytes(data []byte, df gopacket.DecodeFeedback) (res error) {
	var err error
	e.extnBase, err = decodeExtnBase(data, df)
	if err != nil {
		return err
	}
	if err := checkEndToEndExtnNextHdr(e.NextHdr); err != nil {
		return err
	}
	offset := 2
	for offset < e.ActualLen {
		opt, err := decodeTLVOption(data[offset:e.ActualLen])
		if err != nil {
			return err
		}
		e.Options = append(e.Options, (*EndToEndOption)(opt))
		offset += opt.ActualLength
	}
	return nil
}

// @ trusted
// @ requires false
func decodeEndToEndExtn(data []byte, p gopacket.PacketBuilder) error {
	e := &EndToEndExtn{}
	err := e.DecodeFromBytes(data, p)
	p.AddLayer(e)
	if err != nil {
		return err
	}
	return p.NextDecoder(scionNextLayerTypeAfterE2E(e.NextHdr))
}

// @ ensures (err != nil) == (t == HopByHopClass || t == End2EndClass)
// @ ensures err != nil ==> err.ErrorMem()
// @ decreases
func checkEndToEndExtnNextHdr(t L4ProtocolType) (err error) {
	if t == HopByHopClass {
		return serrors.New("e2e extension must not come before the HBH extension")
	} else if t == End2EndClass {
		return serrors.New("e2e extension must not be repeated")
	}
	return nil
}

// SerializeTo implementation according to gopacket.SerializableLayer
// (VerifiedSCION) Serialization of extensions is never invoked in the router
// @ requires false
func (e *EndToEndExtn) SerializeTo(b gopacket.SerializeBuffer,
	opts gopacket.SerializeOptions) error {

	if err := checkEndToEndExtnNextHdr(e.NextHdr); err != nil {
		return err
	}

	o := make([]*tlvOption, 0, len(e.Options))
	for _, v := range e.Options {
		o = append( /*@ perm(0/1), @*/ o, (*tlvOption)(v))
	}

	return e.extnBase.serializeToWithTLVOptions(b, opts, o)
}

// FindOption returns the first option entry of the given type if any exists,
// or ErrOptionNotFound otherwise.
// (VerifiedSCION) FindOption is never called in the router.
// @ requires false
func (e *EndToEndExtn) FindOption(typ OptionType) (*EndToEndOption, error) {
	for _, o := range e.Options {
		if o.OptType == typ {
			return o, nil
		}
	}
	return nil, ErrOptionNotFound
}

// HopByHopExtnSkipper is a DecodingLayer which decodes a HopByHop extension
// without parsing its content.
// This can be used with a DecodingLayerParser to handle SCION packets which
// may or may not have a HopByHop extension.
type HopByHopExtnSkipper struct {
	extnBase
}

// DecodeFromBytes implementation according to gopacket.DecodingLayer
// @ requires  sl.AbsSlice_Bytes(data, 0, len(data))
// @ requires  s.NonInitMem()
// @ requires  df != nil
// @ preserves df.Mem()
// @ ensures   res == nil ==> s.Mem(data)
// @ ensures   res != nil ==> (s.NonInitMem() && res.ErrorMem())
// @ ensures   res != nil ==> sl.AbsSlice_Bytes(data, 0, len(data))
// @ decreases
func (s *HopByHopExtnSkipper) DecodeFromBytes(data []byte, df gopacket.DecodeFeedback) (res error) {
	var err error
	// @ unfold s.NonInitMem()
	s.extnBase, err = decodeExtnBase(data, df)
	if err != nil {
		// @ fold s.NonInitMem()
		return err
	}
	if err := checkHopByHopExtnNextHdr(s.NextHdr); err != nil {
		// @ fold s.NonInitMem()
		return err
	}
	// @ ghost contentsLen := s.extnBase.ActualLen
	// @ sl.SplitByIndex_Bytes(data, 0, len(data), contentsLen, writePerm)
	// @ sl.Reslice_Bytes(data, 0, contentsLen, writePerm)
	// @ sl.Reslice_Bytes(data, contentsLen, len(data), writePerm)
	// @ assert sl.AbsSlice_Bytes(s.extnBase.Contents, 0, len(s.extnBase.Contents))
	// @ assert sl.AbsSlice_Bytes(s.extnBase.Payload, 0, len(s.extnBase.Payload))
	// @ assert acc(&s.extnBase)
	// @ fold s.extnBase.BaseLayer.Mem(data)
	// @ fold s.extnBase.Mem(data)
	// @ fold s.Mem(data)
	return nil
}

// @ pure
// @ decreases
func (e *HopByHopExtnSkipper) LayerType() gopacket.LayerType {
	return LayerTypeHopByHopExtn
}

// @ decreases
func (s *HopByHopExtnSkipper) CanDecode() gopacket.LayerClass {
	return LayerClassHopByHopExtn
}

// @ preserves acc(h.Mem(ubuf), def.ReadL20)
// @ decreases
func (h *HopByHopExtnSkipper) NextLayerType( /*@ ghost ubuf []byte @*/ ) gopacket.LayerType {
	return scionNextLayerTypeAfterHBH( /*@ unfolding acc(h.Mem(ubuf), def.ReadL20) in (unfolding acc(h.extnBase.Mem(ubuf), def.ReadL20) in @*/ h.NextHdr /*@ ) @*/)
}

// EndToEndExtnSkipper is a DecodingLayer which decodes an EndToEnd extension
// without parsing its content.
// This can be used with a DecodingLayerParser to handle SCION packets which
// may or may not have an EndToEnd extension.
type EndToEndExtnSkipper struct {
	extnBase
}

// DecodeFromBytes implementation according to gopacket.DecodingLayer
// @ requires  sl.AbsSlice_Bytes(data, 0, len(data))
// @ requires  s.NonInitMem()
// @ requires  df != nil
// @ preserves df.Mem()
// @ ensures   res == nil ==> s.Mem(data)
// @ ensures   res != nil ==> (s.NonInitMem() && res.ErrorMem())
// @ ensures   res != nil ==> sl.AbsSlice_Bytes(data, 0, len(data))
// @ decreases
func (s *EndToEndExtnSkipper) DecodeFromBytes(data []byte, df gopacket.DecodeFeedback) (res error) {
	var err error
	// @ unfold s.NonInitMem()
	s.extnBase, err = decodeExtnBase(data, df)
	if err != nil {
		// @ fold s.NonInitMem()
		return err
	}
	if err := checkEndToEndExtnNextHdr(s.NextHdr); err != nil {
		// @ fold s.NonInitMem()
		return err
	}
	// @ ghost contentsLen := s.extnBase.ActualLen
	// @ sl.SplitByIndex_Bytes(data, 0, len(data), contentsLen, writePerm)
	// @ sl.Reslice_Bytes(data, 0, contentsLen, writePerm)
	// @ sl.Reslice_Bytes(data, contentsLen, len(data), writePerm)
	// @ assert sl.AbsSlice_Bytes(s.extnBase.Contents, 0, len(s.extnBase.Contents))
	// @ assert sl.AbsSlice_Bytes(s.extnBase.Payload, 0, len(s.extnBase.Payload))
	// @ assert acc(&s.extnBase)
	// @ fold s.extnBase.BaseLayer.Mem(data)
	// @ fold s.extnBase.Mem(data)
	// @ fold s.Mem(data)
	return nil
}

// @ pure
// @ decreases
func (e *EndToEndExtnSkipper) LayerType() gopacket.LayerType {
	return LayerTypeEndToEndExtn
}

// @ decreases
func (s *EndToEndExtnSkipper) CanDecode() gopacket.LayerClass {
	return LayerClassEndToEndExtn
}

// @ preserves acc(e.Mem(ubuf), def.ReadL20)
// @ decreases
func (e *EndToEndExtnSkipper) NextLayerType( /*@ ghost ubuf []byte @*/ ) gopacket.LayerType {
	return scionNextLayerTypeAfterE2E( /*@ unfolding acc(e.Mem(ubuf), def.ReadL20) in (unfolding acc(e.extnBase.Mem(ubuf), def.ReadL20) in @*/ e.NextHdr /*@ ) @*/)
}
