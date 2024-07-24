// Goal of this file:
//   Curently, Gobra's support for resoning about the values of bitwise operations is very limited.
//   While this is not addressed, we rely on Dafny to prove that the lemmas hold, and we just provide
//   an axiomatized version of the Lemma in Gobra. This is sub-optimal, but it is less than nothing.

// How to extend:
//   When a new lemma is needed, we should prove it in this file. If the lemma
//   applies to Go's int type, we should introduce a lemma for when int has 32bit
//   and for when it has 64bit.

lemma ByteValue(b: bv8)
	ensures 0 <= (b as int) && (b as int) < 256
{}

lemma BitAnd3_32bit(b: bv32)
	ensures var res := b & 0x3;
		0 <= res && res <= 3  &&
		(b == 0 ==> res == 0) &&
		(b == 3 ==> res == 3) &&
		(b == 4 ==> res == 0)
{}

lemma BitAnd3_64bit(b: bv64)
	ensures var res := b & 0x3;
		0 <= res <= 3  &&
		(b == 0 ==> res == 0) &&
		(b == 3 ==> res == 3) &&
		(b == 4 ==> res == 0)
{}

lemma BitAnd7_32bit(b: bv32)
	ensures var res := b & 0x7;
		0 <= res <= 7
{}

lemma BitAnd7_64bit(b: bv64)
	ensures var res := b & 0x7;
		0 <= res <= 7
{}

lemma Shift30LessThan4(b: bv32)
	ensures var res := b >> 30;
		0 <= res <= 3
{}

lemma And3fAtMost64(b: bv8)
	ensures var res := b & 0x3F;
		0 <= res < 64
{}

datatype MetaHdr = MetaHdr(
	CurrINF: bv8,
	CurrHF:  bv8,
	SegLen0: bv8,
	SegLen1: bv8,
	SegLen2: bv8
)

function InBounds(m: MetaHdr): bool {
	// each of the following conditions is essential for
	// proving SerializeAndDeserializeLemma
	0 <= m.CurrINF <= 3  &&
	0 <= m.CurrHF  <= 63 &&
	0 <= m.SegLen0 <= 63 &&
	0 <= m.SegLen1 <= 63 &&
	0 <= m.SegLen2 <= 63
}

function Uint32Spec(b0: bv8, b1: bv8, b2: bv8, b3: bv8): bv32 {
	(b3 as bv32) | ((b2 as bv32)<<8) | ((b1 as bv32)<<16) | ((b0 as bv32)<<24)
}

function PutUint32Spec(b0: bv8, b1: bv8, b2: bv8, b3: bv8, v: bv32): bool {
	var mask: bv32 := 0x000000FF;
	&& b0 == ((v >> 24) & mask) as bv8
	&& b1 == ((v >> 16) & mask) as bv8
	&& b2 == ((v >> 8) & mask) as bv8
	&& b3 == (v & mask) as bv8
}

function DecodedFrom(line: bv32): MetaHdr {
	MetaHdr(
		(line >> 30) as bv8,
		((line>>24) & 0x3F) as bv8,
		((line>>12) & 0x3F) as bv8,
		((line>>6) & 0x3F) as bv8,
		(line & 0x3F) as bv8
	)
}

function SerializedToLine(m: MetaHdr): bv32 {
	((m.CurrINF as bv32) << 30) |
	(((m.CurrHF & 0x3F) as bv32)<<24) |
	(((m.SegLen0 & 0x3F) as bv32) << 12) |
	(((m.SegLen1 & 0x3F) as bv32) << 6) |
	((m.SegLen2 & 0x3F) as bv32)
}

lemma SerializeAndDeserializeLemma(m: MetaHdr, b0: bv8, b1: bv8, b2: bv8, b3: bv8)
	requires InBounds(m)
	ensures var line := SerializedToLine(m);
		PutUint32Spec(b0, b1, b2, b3, line) ==> (DecodedFrom(Uint32Spec(b0, b1, b2, b3)) == m)
{}

lemma SerializeAndDeserializeMetaHdrLemma(m: MetaHdr)
	requires InBounds(m)
	ensures  DecodedFrom(SerializedToLine(m)) == m
{}

lemma InfoFieldFirstByteSerializationLemmas()
	// or
	ensures 0 as bv8 | 1 == 1
	ensures 0 as bv8 | 2 == 2
	ensures 1 as bv8 | 2 == 3
	// and
	ensures 0 as bv8 & 1 == 0
	ensures 0 as bv8 & 2 == 0
	ensures 1 as bv8 & 1 == 1
	ensures 1 as bv8 & 2 == 0
	ensures 2 as bv8 & 1 == 0
	ensures 2 as bv8 & 2 == 2
	ensures 3 as bv8 & 1 == 1
	ensures 3 as bv8 & 2 == 2
{}


// Functional specs for encoding/binary (BigEndian)
function FUint16Spec(b0: bv8, b1: bv8): bv16 {
	(b1 as bv16) | ((b0 as bv16) << 8)
}

function FPutUint16Spec(v: bv16): (bv8, bv8) {
	((v >> 8) as bv8, (v & 0xFF) as bv8)
}

lemma FUint16AfterFPutUint16(v: bv16)
	ensures var (b0, b1) := FPutUint16Spec(v);
		FUint16Spec(b0, b1) == v
{}

lemma FPutUint16AfterFUint16(b0: bv8, b1: bv8)
	ensures var v := FUint16Spec(b0, b1);
		FPutUint16Spec(v) == (b0, b1)
{}

function FUint32Spec(b0: bv8, b1: bv8, b2: bv8, b3: bv8): bv32 {
	(b3 as bv32) | ((b2 as bv32) << 8) | ((b1 as bv32) << 16) | ((b0 as bv32) << 24)
}

function FPutUint32Spec(v: bv32): (bv8, bv8, bv8, bv8) {
	(((v >> 24) & 0xFF) as bv8,
	((v >> 16) & 0xFF) as bv8,
	((v >> 8) & 0xFF) as bv8,
	(v & 0xFF) as bv8)
}

lemma FUint32AfterFPutUint32(v: bv32)
	ensures var (b0, b1, b2, b3) := FPutUint32Spec(v);
		FUint32Spec(b0, b1, b2, b3) == v
{}

lemma FPutUint32AfterFUint32(b0: bv8, b1: bv8, b2: bv8, b3: bv8)
	ensures var v := FUint32Spec(b0, b1, b2, b3);
		FPutUint32Spec(v) == (b0, b1, b2, b3)
{}

lemma FoldChecksumLemma(csum: bv32)
	ensures csum > 0xffff ==>
		var newCsum := (csum >> 16) + (csum & 0xffff);
		newCsum < csum
{}