# Plan: parsing packet bytes through `seq[byte]` views instead of slices + permissions

> **Status: implemented on this branch** (commits following this document).
> All four steps below are executed: `View` and the strengthened slice lemmas
> are in `verification/utils/slices`, the parsers in `pkg/slayers/path`,
> `pkg/slayers/path/scion`, `pkg/slayers` and `router` operate on views, and
> the OffsetEq/Widen/Subslice scaffolding is deleted or reduced to pure
> sequence lemmas. Deviations from the letter of the plan: `CurrSeg` keeps its
> packet-relative signature (offsets into the view) rather than taking
> field-exact arguments, the `*WithInfo` family is kept (seq-based) instead of
> merged, and heap-boundary predicates (`(*SCION).EqAbsHeader`,
> `CorrectlyDecoded*`, `ValidHeaderOffset`) keep a buffer argument for `Mem`
> while their contents-reasoning goes through views. The proofs have not yet
> been run through Gobra; CI is the arbiter for the proof scaffolding
> (asserts/triggers), which may need iteration.

## Problem

Ghost pure functions that parse packet fields currently take a `[]byte` plus offsets and
require `sl.Bytes(raw, 0, len(raw))` (or elementwise `acc(&raw[i])`) in their preconditions.
For example, `Timestamp` in `pkg/slayers/path/infofield_spec.gobra`:

```gobra
ghost
requires 0 <= currINF && 0 <= headerOffset
requires InfoFieldOffset(currINF, headerOffset) + InfoLen < len(raw)
requires sl.Bytes(raw, 0, len(raw))
decreases
pure func Timestamp(raw []byte, currINF int, headerOffset int) io.Ainfo
```

Because a pure function cannot perform ghost operations (`SplitRange_Bytes`,
`Reslice_Bytes`, ...), a caller holding `sl.Bytes(raw, 0, len(raw))` cannot manufacture the
predicate instance for a sub-range inside a pure context. The consequence is that *every*
function in the parsing chain must take the entire buffer plus offsets, and every
relationship between "parsed from the full buffer" and "parsed from a subslice" needs a
bespoke lemma (`BytesToAbsInfoFieldOffsetEq`, `WidenBytesHopField`, `WidenCurrSeg`,
`absIO_valWidenLemma`, `ValidPktMetaHdrSublice`, `IsSupportedPktSubslice`,
`AbsPktToSubSliceAbsPkt`, ...). These lemmas are pure permission plumbing: they unfold two
predicate instances, re-prove pointer overlap with `sl.AssertSliceOverlap`, and re-fold.

The fix: separate *heap access* from *parsing*. Heap access is concentrated in a single
heap-dependent, opaque function (`View`) that abstracts a `sl.Bytes` range into a
mathematical `seq[byte]`. All parsing functions become permission-free pure functions over
`seq[byte]`, taking exactly the bytes of the field they parse. Sub-ranging then happens at
the sequence level (`v[a:b]`), where it is definitional, instead of at the permission level,
where it requires ghost statements.

The codebase already anticipates this in places:
- `seqs.ToSeqByte(ub []byte) seq[byte]` (`verification/utils/seqs/seqs.gobra:48`) is an
  abstract view function, characterized elementwise via `sl.GetByte`.
- `slayers.IsSupportedRawPkt(raw seq[byte])` (`pkg/slayers/scion_spec.gobra`) is a parsing
  function already written over `seq[byte]`, used through `SerializeBuffer.View()`.
- `raw_spec.gobra:378` carries a `// TODO: rename this to View()` on `absPkt`.
- `binary.BigEndian.Uint16Spec/Uint32Spec` are already permission-free byte-level
  functions, so no changes to the `encoding/binary` stubs are needed for reading.

## Step 1 — `View` in `verification/utils/slices`

Add to `verification/utils/slices/slices.gobra`:

```gobra
ghost
opaque
requires acc(Bytes(s, start, end), _)
ensures  len(res) == end - start
ensures  forall i int :: { res[i] } 0 <= i && i < end - start ==>
	res[i] == GetByte(s, start, end, start + i)
decreases
pure func View(s []byte, start int, end int) (res seq[byte]) {
	return unfolding acc(Bytes(s, start, end), _) in ViewAux(s, start, end)
}

// Helper over raw quantified permissions (same style as BytesToAbsInfoFieldHelper),
// so that the recursion does not need per-range predicate instances.
ghost
requires 0 <= i && i <= end
requires forall k int :: { &s[k] } i <= k && k < end ==> acc(&s[k], _)
ensures  len(res) == end - i
ensures  forall k int :: { res[k] } 0 <= k && k < end - i ==> res[k] == s[i + k]
decreases end - i
pure func ViewAux(s []byte, i int, end int) (res seq[byte]) {
	return i == end ? seq[byte]{} : seq[byte]{s[i]} ++ ViewAux(s, i + 1, end)
}
```

Notes:
- The postconditions of an `opaque` function remain visible, so the elementwise
  characterization (`View(s, start, end)[i] == GetByte(s, start, end, start+i)`) is
  available everywhere without `reveal`. In practice callers should almost never need
  `reveal View(...)`.
- The wildcard permission amount (`acc(Bytes(...), _)`) lets the function be applied under
  any fraction (`R55`, etc.) without threading a `perm` argument. This matches
  `seqs.ToSeqByte`.
- `View` is deliberately indexed by the *predicate instance* `Bytes(s, start, end)`. A
  caller holding `Bytes(s, 0, len(s))` writes `View(s, 0, len(s))[a:b]` for a sub-range —
  a pure sequence operation — instead of splitting predicates. This is the key move that
  eliminates the ghost-operation-in-pure-context problem.
- Framing is by the heap: as long as the caller's fraction of `Bytes(s, start, end)` is
  preserved (not unfolded and modified), `View(s, start, end)` is automatically known to
  be unchanged.
- If the recursive body turns out to be brittle in verification, fall back to declaring
  `View` abstract (bodyless) with the same postconditions — this is exactly the (already
  trusted) `seqs.ToSeqByte` pattern, generalized with `start`/`end`. In either variant,
  `seqs.ToSeqByte(ub)` becomes a deprecated alias for `View(ub, 0, len(ub))` and should be
  removed at the end of the migration (its only current use is
  `gopacket.SerializeBuffer.View()` in
  `verification/dependencies/github.com/google/gopacket/writer.gobra`, which should be
  re-specified in terms of `sl.View`).

Additionally, add one extensionality lemma that converts elementwise knowledge into
sequence equality (needed after buffer writes, see Step 4):

```gobra
ghost
requires acc(Bytes(s, start, end), _)
requires len(other) == end - start
requires forall i int :: { other[i] } 0 <= i && i < end - start ==>
	other[i] == GetByte(s, start, end, start + i)
ensures  View(s, start, end) == other
decreases
func ViewEqFromElements(s []byte, start int, end int, other seq[byte])
```

## Step 2 — strengthen the specs of the `slices` package

Every ghost operation that transfers permissions between predicate instances must now also
state what happens to the views, so that clients never lose contents information when they
split/combine/reslice. Concretely, extend the postconditions:

```gobra
// SplitByIndex_Bytes gains:
ensures View(s, start, idx) == old(View(s, start, end))[:idx - start]
ensures View(s, idx, end)   == old(View(s, start, end))[idx - start:]

// CombineAtIndex_Bytes gains:
ensures View(s, start, end) == old(View(s, start, idx)) ++ old(View(s, idx, end))

// Reslice_Bytes gains:
ensures View(s[start:end], 0, end - start) == old(View(s, start, end))

// Unslice_Bytes gains:
ensures View(s, start, end) == old(View(s[start:end], 0, end - start))

// SplitRange_Bytes gains:
ensures View(s[start:end], 0, end - start) == old(View(s, 0, len(s)))[start:end]
ensures View(s, 0, start)                  == old(View(s, 0, len(s)))[:start]
ensures View(s, end, len(s))               == old(View(s, 0, len(s)))[end:]

// CombineRange_Bytes gains:
ensures View(s, 0, len(s)) ==
	old(View(s, 0, start)) ++ old(View(s[start:end], 0, end - start)) ++ old(View(s, end, len(s)))
```

All of these follow from the elementwise postcondition of `View` plus the pointer-identity
facts the lemma bodies already establish (`&s[start:end][i] == &s[start+i]`); where the
prover needs help, close with `ViewEqFromElements`.

With these in place, the generic fact that today is re-proved once per parsing function
(every `*OffsetEq` / `Widen*` / `*Subslice` lemma) is available once and for all:
**the view of a subslice is the subsequence of the view.**

## Step 3 — refactor the parsing functions to take `seq[byte]`

General shape: each parser takes exactly the bytes of the thing it parses, with a length
precondition instead of offset arithmetic and permissions. Offsets survive only in the
*callers*, as sequence slicing.

### 3a. Leaf parsers — `pkg/slayers/path`

`infofield_spec.gobra` (`InfoLen == 8`):

```gobra
ghost
requires len(raw) == InfoLen
decreases
pure func ConsDir(raw seq[byte]) bool { return raw[0] & 0x1 == 0x1 }

ghost
requires len(raw) == InfoLen
decreases
pure func Peer(raw seq[byte]) bool { return raw[0] & 0x2 == 0x2 }

ghost
requires len(raw) == InfoLen
decreases
pure func Timestamp(raw seq[byte]) io.Ainfo {
	return io.Ainfo{uint(binary.BigEndian.Uint32Spec(raw[4], raw[5], raw[6], raw[7]))}
}

ghost
requires len(raw) == InfoLen
decreases
pure func AbsUinfo(raw seq[byte]) set[io.MsgTerm] {
	return AbsUInfoFromUint16(binary.BigEndian.Uint16Spec(raw[2], raw[3]))
}

ghost
opaque
requires len(raw) == InfoLen
decreases
pure func BytesToAbsInfoField(raw seq[byte]) io.AbsInfoField {
	return io.AbsInfoField {
		AInfo:   Timestamp(raw),
		UInfo:   AbsUinfo(raw),
		ConsDir: ConsDir(raw),
		Peer:    Peer(raw),
	}
}
```

Note the switch from `binary.BigEndian.Uint32` (slice + permissions) to
`binary.BigEndian.Uint32Spec` (byte values): the `unfolding`, the `AssertSliceOverlap`
calls, and `BytesToAbsInfoFieldHelper` all disappear. `InfoFieldOffset` stays — callers
still use it to *select* the sub-sequence.

`hopfield_spec.gobra` (`HopLen == 12`, `MacLen == 6`):

```gobra
ghost
requires len(raw) == HopLen
decreases
pure func BytesToIO_HF(raw seq[byte]) io.HF {
	return let inif2 := binary.BigEndian.Uint16Spec(raw[2], raw[3]) in
		let egif2 := binary.BigEndian.Uint16Spec(raw[4], raw[5])    in
		io.HF {
			InIF2: ifsToIO_ifs(inif2),
			EgIF2: ifsToIO_ifs(egif2),
			HVF:   AbsMac(FromSeqToMacArray(raw[6:6+MacLen])),
		}
}
```

with a new permission-free companion to `FromSliceToMacArray` in `io_msgterm_spec.gobra`:

```gobra
ghost
requires len(mac) == MacLen
ensures  forall i int :: { res[i] } 0 <= i && i < MacLen ==> mac[i] == res[i]
decreases
pure func FromSeqToMacArray(mac seq[byte]) (res [MacLen]byte) {
	return [MacLen]byte{ mac[0], mac[1], mac[2], mac[3], mac[4], mac[5] }
}
```

### 3b. Mid-level parsers — `pkg/slayers/path/scion/raw_spec.gobra`

These functions parse *several* fields, so they take the view of the region they cover
(for the top-level ones: the whole packet) and slice it. All permissions vanish; offset
parameters survive only where they select sub-sequences.

```gobra
ghost
requires 0 <= currHfIdx && currHfIdx <= segLen
requires len(hfBytes) == segLen * path.HopLen
ensures  len(res) == segLen - currHfIdx
decreases segLen - currHfIdx
pure func hopFields(hfBytes seq[byte], currHfIdx int, segLen int) (res seq[io.HF]) {
	return currHfIdx == segLen ? seq[io.HF]{} :
		seq[io.HF]{path.BytesToIO_HF(hfBytes[currHfIdx*path.HopLen:(currHfIdx+1)*path.HopLen])} ++
		hopFields(hfBytes, currHfIdx + 1, segLen)
}
```

`segment` takes `hfBytes seq[byte]` the same way. `CurrSeg` merges with the
`CurrSegWithInfo` family from `info_hop_setter_lemmas.gobra`: since the info field is now
parsed independently of permissions, there is no reason to keep two variants ("parse info
from raw" vs. "info passed as value"):

```gobra
ghost
opaque
requires 0 < segLen
requires 0 <= currHfIdx && currHfIdx <= segLen
requires len(infoBytes) == path.InfoLen
requires len(hfBytes) == segLen * path.HopLen
decreases
pure func CurrSeg(infoBytes seq[byte], hfBytes seq[byte], currHfIdx int, segLen int) io.Seg {
	return segment(hfBytes, currHfIdx,
		path.Timestamp(infoBytes), path.AbsUinfo(infoBytes),
		path.ConsDir(infoBytes), path.Peer(infoBytes), segLen)
}
```

(If keeping the packet-relative signature is preferred for fewer call-site changes,
`CurrSeg(raw seq[byte], offset, currInfIdx, currHfIdx, segLen, headerOffset)` with
`raw[...]` slicing inside is also permission-free; the field-exact variant above is the
end state the refactor aims for, and `CurrSegWithInfo`'s existence shows it is the shape
proofs actually want.)

`LeftSeg` / `RightSeg` / `MidSeg` / `absPkt` / `RawBytesToMetaHdr` / `RawBytesToBase` /
`validPktMetaHdr` take `raw seq[byte]` (the whole packet view) and compute the
`infoBytes`/`hfBytes` arguments by pure slicing with the existing offset functions
(`path.InfoFieldOffset`, `HopFieldOffset`). E.g.:

```gobra
ghost
requires MetaLen <= len(raw)
decreases
pure func RawBytesToMetaHdr(raw seq[byte]) MetaHdr {
	return DecodedFrom(binary.BigEndian.Uint32Spec(raw[0], raw[1], raw[2], raw[3]))
}
```

Method specs keep the buffer argument for the *predicate*, and pass views to the abstract
functions: `(s *Raw) absPkt(ub []byte)` becomes `(s *Raw) absPkt(raw seq[byte])` and call
sites use `s.absPkt(sl.View(ub, 0, len(ub)))`. Where an `ub` and its prefix `ub[:length]`
both appear today, both are now expressed from one view (`V := sl.View(ub, 0, len(ub))`;
prefix is `V[:length]`) — this is what kills the widening lemmas.

The `CorrectlyDecodedInf/Hf(WithIdx)` family keeps its `(ub []byte)` receiver-style
signature at the boundary or moves to `seq[byte]`; either way its body compares against
`BytesToAbsInfoField(V[infOffset:infOffset+path.InfoLen])` with `V := sl.View(ub, 0, len(ub))`.

### 3c. Header-level parsers — `pkg/slayers/scion_spec.gobra` and `router/io-spec.gobra`

- `ValidPktMetaHdr(ub []byte)`, `IsSupportedPkt(ub []byte)`, `GetAddressOffset*`,
  `GetLength*`, `GetPathType`, `GetNextHdr` → take `raw seq[byte]`. `IsSupportedPkt` is
  simply deleted in favor of the already existing `IsSupportedRawPkt(raw seq[byte])`
  (rename it to `IsSupportedPkt` once the slice version is gone).
- `router/io-spec.gobra`: `absPkt(raw seq[byte]) io.Pkt`,
  `absIO_val(raw seq[byte], ingressID uint16) io.Val`,
  `absValUnsupported` loses its `sl.Bytes` precondition entirely.
  `MsgToAbsVal` remains heap-dependent (it looks inside `msg.Mem()`) and becomes the/an
  explicit boundary: it extracts the buffer, applies `sl.View`, and calls `absIO_val`.
- Loop invariants and contracts in `router/dataplane.go` that currently say
  `absIO_val(rawPkt, ingressID)` become `absIO_val(sl.View(rawPkt, 0, len(rawPkt)), ingressID)`.
  This is the bulk of the (mechanical) call-site churn: ~150 references in
  `router/dataplane.go`, plus `pkg/slayers/path/scion/raw.go`, `decoded.go`, `scion.go`.

## Step 4 — lemma cleanup: deletions and additions

### Deleted (made redundant by seq-level sub-ranging)

| Lemma | File |
|---|---|
| `BytesToAbsInfoFieldOffsetEq`, `BytesToAbsInfoFieldHelper` | `pkg/slayers/path/infofield_spec.gobra` |
| `WidenBytesHopField`, `BytesToAbsHopFieldOffsetEq` | `pkg/slayers/path/hopfield_spec.gobra` |
| `WidenCurrSeg`, `WidenLeftSeg`, `WidenRightSeg`, `WidenMidSeg` | `pkg/slayers/path/scion/widen-lemma.gobra` (whole file) |
| `CurrSegEquality`, `LeftSegEquality(Spec)`, `RightSegEquality(Spec)`, `MidSegEquality(Spec)`, and the `CurrSegWithInfo`/`LeftSegWithInfo`/`RightSegWithInfo`/`MidSegWithInfo` duplicates | `pkg/slayers/path/scion/info_hop_setter_lemmas.gobra` (family merges into `CurrSeg` et al.) |
| `ValidPktMetaHdrSublice` | `pkg/slayers/path/scion/raw_spec.gobra` |
| `IsSupportedPktSubslice`, `ValidHeaderOffsetToSubSliceLemma`, `ValidHeaderOffsetFromSubSliceLemma` | `pkg/slayers/scion_spec.gobra` |
| `absIO_valWidenLemma`, `ValidPktMetaHdrWidenLemma`, `IsSupportedPktWidenLemma`, `absPktWidenLemma` | `router/widen-lemma.gobra` (whole file) |
| `AbsPktToSubSliceAbsPkt`, `SubSliceAbsPktToAbsPkt` | `router/io-spec-lemmas.gobra` |

Where an opaque function is involved (e.g. `absPkt` on `V` vs. `V[:length]`), a residual
lemma may still be wanted so that call sites don't need `reveal`; such lemmas shrink to a
`reveal` + sequence reasoning with **no** permission manipulation, no `unfold`/`fold`, and
no `AssertSliceOverlap`. Expectation: `router/widen-lemma.gobra` either disappears or
becomes a ~20-line file.

`sl.AssertSliceOverlap` keeps its remaining uses in executable-code proofs (where real
subslices are taken), but disappears from all pure parsing definitions.

### Added

1. `View`, `ViewAux`, `ViewEqFromElements` in `verification/utils/slices` (Step 1).
2. The strengthened postconditions of Step 2 (same package).
3. **Write-effect lemmas**: today, setter proofs (`SetInfoField`, `SetHopField`,
   `info_hop_setter_lemmas.gobra`) argue field-by-field which parsing functions survive a
   buffer write. With views, this becomes one generic pattern: after code unfolds
   `Bytes(ub, 0, len(ub))`, writes bytes `[a, b)`, and refolds,

   ```gobra
   sl.View(ub, 0, len(ub)) ==
   	old(sl.View(ub, 0, len(ub)))[:a] ++ written ++ old(sl.View(ub, 0, len(ub)))[b:]
   ```

   which follows from `ViewEqFromElements`. To make this convenient, specify the ghost
   update boundary once, e.g. as a lemma in the `slices` package:

   ```gobra
   ghost
   requires ... // Bytes held, old elementwise facts for [0,a) and [b,len), new bytes for [a,b)
   ensures  View(ub, 0, len(ub)) == oldView[:a] ++ written ++ oldView[b:]
   func ViewAfterUpdate(ub []byte, a int, b int, written seq[byte], oldView seq[byte])
   ```

   The existing `binary.BigEndian.PutUint16/PutUint32` postconditions
   (`PutUint16Spec(b[0], b[1], v)`) already give the elementwise facts needed to
   instantiate `written`.
4. **Seq-index congruence helpers** only if the SMT solver needs nudging, e.g.
   `SubSeqIndex(v seq[byte], a, b, i)` asserting `v[a:b][i] == v[a+i]`. Gobra encodes
   these definitionally for sequences, so start without them and add on demand.
5. Optional convenience: `binary.BigEndian.Uint32SeqSpec(bs seq[byte])` /
   `Uint16SeqSpec(bs seq[byte])` wrappers (`requires len(bs) == 4/2`) to avoid spelling
   out four indices at every use. Pure sugar over `Uint32Spec`.

## Migration strategy

Verification is per-package and expensive, so migrate bottom-up, keeping the build green:

1. **`verification/utils/slices`** — add `View` + Step-2 postconditions; verify the
   package standalone (plus `slices_test.gobra`).
2. **`verification/utils/seqs` / gopacket stubs** — define `ToSeqByte` as
   `View(ub, 0, len(ub))` (or delete it and re-specify `SerializeBuffer.View()` against
   `sl.View`).
3. **`pkg/slayers/path`** — convert leaf parsers (3a). During the transition, if needed,
   keep the old slice-based functions temporarily with bodies delegating to the new ones
   (`Timestamp_old(raw, i, h) == Timestamp(sl.View(raw,0,len(raw))[idx:idx+InfoLen])`), so
   dependent packages keep verifying; delete them at the end. Update
   `hopfield.go`/`infofield.go` proof annotations (`DecodeFromBytes`/`SerializeTo` relate
   the struct to `BytesToIO_HF(sl.View(...)...)`).
4. **`pkg/slayers/path/scion`** — convert `raw_spec.gobra` (3b), merge the `*WithInfo`
   family, delete `widen-lemma.gobra`, rewrite `info_hop_setter_lemmas.gobra` on top of the
   write-effect lemma; update `raw.go`, `base.go`, `decoded.go` annotations.
5. **`pkg/slayers`** — convert `scion_spec.gobra` (3c), delete the subslice lemmas, update
   `scion.go` annotations.
6. **`router`** — convert `io-spec.gobra`, `io-spec-lemmas.gobra`, delete
   `widen-lemma.gobra`, update `dataplane.go` invariants/contracts (mechanical
   `f(raw, ...)` → `f(sl.View(raw, 0, len(raw)), ...)` rewriting, then removal of now-dead
   lemma calls and `SplitRange/CombineRange` choreography that existed only to feed the
   old preconditions).
7. Sweep for dead code: `AssertSliceOverlap` uses in pure functions, unused `Offset`
   helper parameters (`BytesToIO_HF`'s `start`/`end`), stale comments, and the `absPkt`
   TODO at `raw_spec.gobra:378`.

Each step ends with running the package's Gobra verification (CI targets / `Makefile`,
including the chopper configuration re-enabled in #420) before moving up.

## Risks / points of attention

- **Trigger hygiene.** The elementwise postcondition of `View` uses `{ res[i] }` as
  trigger; sequence-heavy proofs can be slower or flakier than pointwise permission
  reasoning in pathological cases. Mitigation: keep big parsers `opaque` (as today) and
  prove equalities via the small set of lemmas rather than raw quantifier reasoning;
  measure verification times per package as part of each migration step.
- **Predicate-instance discipline.** `View(s, a, b)` requires exactly the instance
  `Bytes(s, a, b)`. The convention must be: take the view of the instance you hold, then
  slice the sequence. Code that today holds `Bytes(ub, start, end)` mid-split (e.g. inside
  `DecodeFromBytes` choreography) uses `View(ub, start, end)` at that point and the Step-2
  postconditions to relate it to the outer view when recombining.
- **`decreases` measures.** The recursive `ViewAux` and the seq-based `hopFields` need
  adjusted termination measures (straightforward: `end - i`, `segLen - currHfIdx`).
- **Churn volume.** `router/dataplane.go` alone has ~150 references to `absPkt`/
  `absIO_val`-family functions. The rewrite is mechanical but broad; the temporary-alias
  trick in migration step 3 keeps intermediate states verifiable.
- **What does *not* change.** The `Bytes` predicate itself, the executable code, the
  `encoding/binary` trusted stubs, the IO-spec types (`io.Pkt`, `io.Seg`,
  `io.AbsInfoField`, ...), and the abstract transition relations
  (`router/io-spec-abstract-transitions.gobra`) are untouched — the refactor only moves
  the boundary where bytes stop being heap and become math.
