# Plan: verifying `prepareSCMP` completely (dropping the `TODO()`)

**Ground rule for this plan: the executable Go code cannot be changed.**
Everything below is confined to specifications, predicates, ghost
annotations/arguments (including those embedded in `.go` files as `// @`
comments), `.gobra` files, and the trusted stubs under
`verification/dependencies`. In particular, the
`gopacket.SerializeLayers` call stays, and `p.d.internalIP` is passed to
`SetSrcAddr` as-is.

This document analyzes what it takes to remove the `TODO()` at
`router/dataplane.go:5064` and verify the remainder of
`scionPacketProcessor.prepareSCMP`, i.e., the construction of the SCMP reply
(`scionL`, `scmpH`, `scmpP`, quote) and the call

```go
err = gopacket.SerializeLayers(p.buffer, sopts /*@ , nil @*/, scmpLayers...)
```

whose current specification in
`verification/dependencies/github.com/google/gopacket/writer.gobra` is
`requires false`.

The immediate question that motivated this document: **`SerializeLayers`
requires `layers[i].Mem(layerBufs[i])` for every layer — can we establish
`Mem` for all elements of `scmpLayers`, possibly with a `nil` underlying
buffer?**

---

## 1. Answer to the `Mem` question

**Short answer: no — not with the current predicate definitions, and not for
any choice of buffer, `nil` or otherwise.** For three of the four layers the
*state* of a freshly constructed layer contradicts the predicate body, so no
choice of the `ubuf` argument can make the fold succeed. The predicates were
designed for *decoded* layers (established by `DecodeFromBytes`, which ties
`Contents`/`Payload` to sub-slices of the input buffer); a fresh, about-to-be-
serialized layer has no underlying buffer yet.

However, the predicates can be *generalized* with a `nil`-buffer
("serialize-only") mode, and the codebase already contains all the precedents
needed to do this (see §3). The `(VerifiedSCION) TODO: adapt *SCION.Mem(...)`
comment at `router/dataplane.go:5068` anticipates exactly this.

### 1.1 Per-layer analysis

`scmpLayers = []gopacket.SerializableLayer{&scionL, &scmpH, scmpP}` plus,
when `cause != nil`, `gopacket.Payload(quote)`.

| Layer | `Mem(nil)` foldable? | `Mem(ub)` foldable for some `ub != nil`? | Blocking conjuncts |
|---|---|---|---|
| `gopacket.Payload(quote)` | n/a | **yes**, with `ub := quote` | none — body is `ub === p` (`base.gobra:36`) |
| `scmpP` (e.g. `*SCMPParameterProblem`) | **no** | **no** | `BaseLayer.Mem(ub, 4)` (`scmp_msg_spec.gobra:125`) |
| `&scmpH` (`*SCMP`) | **no** | **no** | `BaseLayer.Mem(ub, 4)` (`scmp_spec.gobra:37`) |
| `&scionL` (`*SCION`) | **no** | **no** | several, see below (`scion_spec.gobra:149`) |

**Why `BaseLayer.Mem` kills `scmpH`/`scmpP` for every buffer.** The body of
`BaseLayer.Mem(ub, breakPoint)` (`pkg/slayers/scion_spec.gobra:244`) is

```gobra
0 <= breakPoint && breakPoint <= len(ub) &&
acc(b) &&
b.Contents === ub[:breakPoint] &&
b.Payload  === ub[breakPoint:]
```

with `breakPoint = 4` (or larger constants for the other SCMP messages):

* `ub == nil`: `4 <= len(nil) = 0` is false. Fold fails on arithmetic alone.
* `ub != nil`: a fresh `slayers.SCMP{TypeCode: typeCode}` has
  `Contents == nil` (length 0). `ub[:4]` has length 4, and `===` on slices
  implies equal lengths, so `Contents === ub[:4]` is unsatisfiable. No ghost
  code can fix this: `Contents` is a real field and only real code (i.e.,
  `DecodeFromBytes`, or the serialization itself) assigns it.

**Why `*SCION.Mem` fails additionally.** For the freshly constructed
`scionL` in `prepareSCMP` (fields assigned at `router/dataplane.go:5067-5085`):

* `s.HdrLen == 0` — it is only ever assigned inside `SerializeTo`'s
  `opts.FixLengths` branch (`pkg/slayers/scion.go:246-250`), which is
  currently dead (`Unreachable()`). Hence
  `CmnHdrLen + s.AddrHdrLenSpecInternal() <= int(s.HdrLen)*LineLen`
  (`scion_spec.gobra:163`) reads `12 + (≥24) <= 0` — false. This is circular:
  `Mem` (as-is) can only hold *after* the serialization that requires it.
* `CmnHdrLen <= len(ubuf)` fails for `ubuf == nil`.
* `s.HeaderMem(ubuf[CmnHdrLen:])` requires `RawDstAddr`/`RawSrcAddr` to be
  sub-slices of `ubuf`; after `SetDstAddr`/`SetSrcAddr`
  (`router/dataplane.go:5079-5084`) they alias the *request packet's* buffer
  (`srcA` comes from `p.scionLayer`) and `p.d.internalIP` respectively — not
  any single fresh buffer.
* `s.Path.Mem(ubuf[CmnHdrLen+...:HdrLen*LineLen])` ties the path's resources
  to a sub-slice of the same `ubuf`, but we hold `revPath.Mem(rawPath)` where
  `rawPath` is a region of the original packet `ub`.

### 1.2 The experiment (what "try it" boils down to)

The negative results above are decidable by inspection (linear arithmetic
over slice lengths plus `===`-injectivity); a Gobra run is not needed to
refute them, but the following snippets make the attempts concrete. The first
three folds fail, the last two succeed:

```gobra
// context: fresh layers as in prepareSCMP
var scionL slayers.SCION            // + field assignments as in prepareSCMP
scmpH := slayers.SCMP{TypeCode: typeCode}

fold scmpH.BaseLayer.Mem(nil, 4)    // FAILS: 4 <= len(nil)
fold scmpH.BaseLayer.Mem(big, 4)    // FAILS: scmpH.Contents === big[:4]
                                    //        (nil vs. length-4 slice)
fold scionL.Mem(nil)                // FAILS: CmnHdrLen <= len(nil), and
                                    //        12 + AddrHdrLen <= HdrLen*LineLen = 0

fold gopacket.Payload(quote).Mem(quote)  // OK: body is `quote === quote`

unfold revPath.Mem(rawPath)         // OK: *scion.Decoded's Mem body
fold   revPath.Mem(nil)             //     never mentions ubuf (see §3)
```

(The failing snippets cannot live in a `*_test.gobra` file in-tree, because
they would fail CI; run them ad hoc when validating this plan. Note that
`pkg/slayers` CI verification takes ~25 min per run,
`.github/workflows/gobra.yml:214-234`. The *positive* counterparts are
committed in-tree as `FoldFreshMem` witness lemmas — see the M1 status note
in §6 — so CI machine-checks that fresh layers satisfy `Mem(nil)` under the
reworked predicates.)

---

## 2. Full inventory of blockers between `TODO()` and `return`

Removing `TODO()` requires all of the following, not just the `Mem` folds:

1. **`SerializeLayers` has no usable spec** (`writer.gobra:105-112`,
   `requires false`, with the note "requires changes to provide access to the
   underlying layers"). The ghost `layerBufs` parameter already exists; the
   call site passes `nil` as a placeholder.
2. **The `SerializableLayer` interface forbids `FixLengths`**
   (`writer.gobra:18`: `requires !opts.FixLengths`), but `prepareSCMP` uses
   `SerializeOptions{ComputeChecksums: true, FixLengths: true}`.
   Correspondingly, `(*SCION).SerializeTo`'s `FixLengths` branch is marked
   `Unreachable()` (`scion.go:246-250`) and must now be verified: it *writes*
   `s.HdrLen` and `s.PayloadLen`, so it needs write permission to those
   fields (the current spec takes only `acc(s.Mem(ubuf), R0)`). (The
   `uint8`/`uint16` casts in that branch generate no proof obligations —
   CI runs with `overflow: '0'`, `.github/workflows/gobra.yml:32` — so no
   buffer-size bound needs to be threaded through the trusted
   `SerializeBuffer` interface.)
3. **`SerializeTo` loses `Mem` on error** (interface post:
   `err == nil ==> Mem(ubuf) && b.Mem()`). `prepareSCMP`'s error path must
   still restore `sl.Bytes(ub, ...)` and `p.buffer.Mem()` to satisfy its own
   postconditions, and the fractions of `ub` carved into the fresh layers'
   predicates would be lost. The implementations (`SCMP.SerializeTo`,
   the SCMP messages) already re-fold `Mem` on every error path, so the
   interface can be strengthened to `preserves`-style without new proof work
   in the bodies.
4. **Double demand on `scionL`'s address bytes.**
   `scmpH.Mem(...)` contains `s.scn != nil ==> s.scn.ChecksumMem()`
   (`scmp_spec.gobra:34-40`), and after
   `scmpH.SetNetworkLayerForChecksum(&scionL)` (`dataplane.go:5089`),
   `s.scn == &scionL`. `ChecksumMem` (`scion_spec.gobra:236-242`) holds
   *full* `acc(&s.RawSrcAddr)`, `acc(&s.RawDstAddr)` and *full*
   `sl.Bytes(...)` of both — while a serialize-mode `scionL.Mem(nil)` also
   needs (at least read) access to the same locations for
   `SerializeAddrHdr`. Both predicates must coexist inside the
   `SerializeLayers` call, so the permission amounts must be split
   (fractions), or the bytes moved into exactly one of the two.
5. **`p.d.internalIP` is only available at wildcard permission.**
   The processor holds `acc(p.d.Mem(), _)`, so the bytes of
   `p.d.internalIP` (used by `SetSrcAddr(&net.IPAddr{IP: p.d.internalIP})`,
   `dataplane.go:5082`) can only ever be obtained at wildcard amount. A
   predicate that stores a *concrete* fraction of `RawSrcAddr`'s bytes is
   therefore unfoldable here, and a wildcard-typed requires clause is lossy
   for the *other* address (whose bytes come from `ub` and must be returned
   at full permission). See §4.3 for the options.
6. **Missing frame in `prepareSCMP`'s own spec**: no permissions for
   `p.rawPkt` (read at `dataplane.go:5110` for the quote), no resources for
   `scmpP` (the spec at `dataplane.go:4900-4919` does not mention it at
   all), and the same for `packSCMP` (`dataplane.go:2181`) and its ~9 call
   sites, which construct `scmpP` as fresh literals
   (e.g. `&slayers.SCMPParameterProblem{...}`, `dataplane.go:2422`).
7. **The IO-level postcondition** `result != nil ==>
   !slayers.IsSupportedPkt(result)` (`dataplane.go:4917-4918`) is currently
   assumed via the `TODO()`. It must be *derived* from serialization. The
   existing mechanism (`scion.go:225-226`:
   `IsSupportedRawPkt(b.View()) == old(IsSupportedPkt(ubuf))`) is unusable
   here because there is no meaningful old buffer; a new route is needed
   (§4.6). Note `IsSupportedPkt` (`scion_spec.gobra:503-509`) is simply
   "path type is `scion.PathType` **and** `NextHdr != L4SCMP`" over the raw
   bytes — and `prepareSCMP` sets `scionL.NextHdr = slayers.L4SCMP`, so the
   packet is unsupported by construction; we only need the specs to carry
   the fact that byte 4 of the output equals `uint8(s.NextHdr)`.
8. **Misc**: `fold`ing `scmpError`'s `ErrorMem` for the success-with-error
   return (`dataplane.go:5122`), bounds for the `hdrLen` computation
   (`dataplane.go:5101-5109`, calling `AddrHdrLen(nil, false)` and
   `Path.Len(nil)` on the *fresh* layer — consistent with the `nil`-mode
   design below), and re-establishing `sl.Bytes(ub, 0, len(ub))` by
   recombining all split ranges on every path.

---

## 3. Enabling observations (why a `nil`-mode design works)

1. **`(*scion.Decoded).Mem(ubuf)` never mentions `ubuf`**
   (`pkg/slayers/path/scion/decoded_spec.gobra:39-48`): it holds
   `Base.Mem()`, `InfoFields`, `HopFields` — all struct-internal. Hence
   `revPath.Mem(rawPath)` can be re-folded as `revPath.Mem(nil)` — the
   lemma for this already exists (`(*Decoded).Widen`, at the end of
   `decoded_spec.gobra`) — and `(*Decoded).SerializeTo(b, ubuf)`
   (`decoded.go:128-133`) as well as `Len(ubuf)` already work fine with
   `ubuf = nil` (`sl.Bytes(nil, 0, 0)` is trivially foldable — precedent in
   `packSCMP`, `dataplane.go:2206`). **The reversed path is already fully
   buffer-independent.**
2. **`Mem(nil)` is an established idiom**: `empty.Path`
   (`pkg/slayers/path/empty/empty_spec_test.gobra:26`), and `decodeLayers`'
   postconditions explicitly produce `opts[i].Mem(nil)` for nil payloads
   (`dataplane.go:5159-5160`). Using `ubuf == nil` as the discriminator for
   "fresh / serialize-only" is consistent with existing usage.
3. **The set of `SerializableLayer` implementations is small and closed**:
   `*SCION`, `*SCMP`, the seven `SCMP*` message types, `gopacket.Payload`,
   and the trusted stub `*layers.BFD`. The extension layers do *not*
   implement it (`extn_spec.gobra:163` is commented out; their `SerializeTo`
   is `requires false` and lacks the ghost parameter). Interface-spec
   changes therefore have a bounded, known ripple.
4. **The SCMP message `SerializeTo` bodies never touch `BaseLayer`** — they
   read the semantic fields (`Pointer`, `Identifier`, ...) and write into
   prepended buffer space. Their proofs survive a weakened `BaseLayer`
   conjunct essentially unchanged. The same holds for `SCMP.SerializeTo`.

---

## 4. Proposed design

### 4.1 `nil`-mode `BaseLayer.Mem` (one change, many beneficiaries)

Redefine (`scion_spec.gobra:244`):

```gobra
pred (b *BaseLayer) Mem(ghost ub []byte, ghost breakPoint int) {
    acc(b) &&
    (ub != nil ==> (0 <= breakPoint && breakPoint <= len(ub) &&
                    b.Contents === ub[:breakPoint]           &&
                    b.Payload  === ub[breakPoint:]))
}
```

Consequences:

* `Mem(nil)` becomes foldable for **fresh** `SCMP` and all seven SCMP
  message types with zero changes to their own predicate bodies.
* All *decoded* contexts keep working: wherever the aliasing facts are used,
  `len(data) >= 4` (or similar) is in scope, which implies `data != nil`.
* `LayerPayload(ghost ub)`-style specs that unconditionally state
  `res === ub[start:end]` need either a `ub != nil` precondition or a
  weakened (conditional) postcondition, matching the `gopacket.Layer`
  interface, which is already conditional (`base.gobra:28-29`).
  Fresh layers never have `LayerPayload` called on them in verified code.

### 4.2 Serialize-mode `*SCION.Mem`

Split the body of `(*SCION).Mem(ubuf)` (`scion_spec.gobra:149-187`) into

* unconditional field permissions (as today, incl. the path-pool clauses,
  `acc(&s.Path)`, `s.Path != nil`), and
* `ubuf != nil ==> (` all current buffer-dependent conjuncts: length bounds,
  `Path.Mem(ubuf[...])`, `BaseLayer` ties, `HeaderMem(ubuf[CmnHdrLen:])`,
  one-hop clause `)`, and
* `ubuf == nil ==> (` serialize-mode:
  `s.Path.Mem(nil)` +
  `acc(&s.RawDstAddr)/acc(&s.RawSrcAddr)` +
  length agreement `len(s.RawDstAddr) == s.DstAddrType.Length()` (and src
  analogously) + byte permissions for the two raw addresses (amounts: §4.3)
  `)`.

Notes:

* In serialize mode `HdrLen`/`PayloadLen` are deliberately unconstrained —
  the `FixLengths` branch assigns them.
* The `HalfPerm` split of `DstAddrType`/`SrcAddrType` between `Mem` and
  `HeaderMem` must be revisited: in serialize mode `HeaderMem` is absent, so
  the other halves belong directly to the `ubuf == nil` branch.
* `ValidPathMetaData`, `EqAbsHeader`, etc. are decoded-mode notions; guard
  their `unfolding`s with `ub != nil` where needed.

### 4.3 `ChecksumMem` and the address-byte permission accounting

Constraints discovered in §2 (items 4, 5):

* `scionL.Mem(nil)` (for `SerializeAddrHdr`) and
  `ChecksumMem(scionL)` inside `scmpH.Mem(nil)` (for `computeChecksum`)
  must **coexist**; both only read the raw address bytes.
* `RawDstAddr` bytes come (via `SrcAddr()`) from `ub` — held at **full,
  concrete** permission by `prepareSCMP`, which must return them at full
  permission. So every predicate touching them must use *concrete*
  fractions (wildcards are lossy: once a wildcard is exhaled from a
  concrete amount, full recovery is unprovable).
* `RawSrcAddr` bytes come from `p.d.internalIP` — available **only at
  wildcard** (`acc(p.d.Mem(), _)`), so no concrete fraction of them can
  ever be folded.

Since the code cannot change (no copying of `p.d.internalIP`), the
**asymmetric-fractions design is the only option**: the serialize-mode
predicates must hold the two address-byte resources at *different* amounts,
matching where they come from:

* `RawDstAddr` (aliases the request packet / `srcA`): **concrete
  fraction** (e.g. `R50`), because `prepareSCMP` must hand back
  `sl.Bytes(ub, 0, len(ub))` at full permission and wildcards are
  unrecoverable.
* `RawSrcAddr` (aliases `p.d.internalIP`): **wildcard** (`acc(..., _)`),
  because wildcard is all the processor ever has of `d`'s state.

Concretely:

* Serialize-mode branch of `SCION.Mem(nil)` (§4.2) holds
  `acc(sl.Bytes(s.RawDstAddr, 0, len(s.RawDstAddr)), R50)` and
  `acc(sl.Bytes(s.RawSrcAddr, 0, len(s.RawSrcAddr)), _)`;
  `ChecksumMem` is re-declared with complementary amounts (e.g. the
  other `R50` half for dst, another wildcard for src, and *fractional*
  `acc(&s.RawSrcAddr, ...)`/`acc(&s.RawDstAddr, ...)` field permissions
  instead of today's full ones). Both users only read, so fractions
  suffice. `ChecksumMem`'s only verified users are `prepareSCMP`,
  `SCMP.SerializeTo`/`computeChecksum`, and the `SCMP` predicates
  (`SetNetworkLayerForChecksum` is called nowhere else in verified code),
  so re-fractioning is low-ripple. Its `len % 2 == 0` conjuncts follow
  from `AddrType.Length() ∈ {4, 8, 12, 16}` (small lemma).
  Wildcard amounts inside predicate bodies should be confirmed early with
  a smoke test (see risk §7).
* **`SetSrcAddr` must be called in wildcard mode**: the ghost argument at
  `dataplane.go:5082` changes from `false` to `true` (a ghost-only edit).
  Its wildcard-mode postcondition
  (`scion.go:710`: `acc(sl.Bytes(s.RawSrcAddr, ...), _)`) is exactly what
  the predicate above needs. Two sub-issues to resolve on the way:
  * the wildcard-mode *pre*condition currently demands `acc(src.Mem(), _)`
    — folding `(&net.IPAddr{IP: p.d.internalIP}).Mem()` requires byte
    permissions for `internalIP`, which are only available at wildcard;
    check whether the fold at a wildcard amount goes through, and if not,
    weaken `SetSrcAddr`'s wildcard-mode precondition to take the raw
    components (`acc(&src.IP, R18)` + `acc(sl.Bytes(src.IP, ...), _)`)
    instead of a folded `Mem()`;
  * access to `p.d.internalIP` itself should follow the existing
    dup-invariant getter idiom (`getExternalMem()` at
    `dataplane.go:5029`), i.e., add a `getInternalIPMem()`-style ghost
    getter to `DataPlane` if none exists.
* **`SetDstAddr`'s postconditions are too weak today**: for the
  `!wildcard`, IP-typed case it returns `acc(dst.Mem(), R18)` and says
  nothing about `s.RawDstAddr`'s bytes — the aliasing postconditions are
  commented out (`scion.go:677-680`). To fold the serialize-mode
  predicate we need the `R50` fraction of `sl.Bytes(s.RawDstAddr, ...)`.
  Strengthen the spec (spec-only) to return that fraction directly,
  plus a magic wand restoring `acc(dst.Mem(), R18)` from it, or
  re-enable (a weakened form of) the commented-out aliasing
  postconditions so the caller can carve the fraction out of
  `sl.Bytes(ub, ...)` itself.

The asymmetry does bake `prepareSCMP`'s aliasing situation into
`pkg/slayers`' serialize-mode predicates. That is acceptable: serialize
mode is new (no existing clients), and the BFD sender (§8) — whose source
address has a different origin — can be accommodated later by
generalizing the amounts, not the shape.

### 4.4 `SerializeTo` spec changes (interface + implementations)

In `writer.gobra`'s `SerializableLayer`:

```gobra
requires  opts.FixLengths ==> ubuf == nil     // was: !opts.FixLengths
requires  b != nil && b.Mem()
requires  sl.Bytes(b.UBuf(), 0, len(b.UBuf()))
requires  Mem(ubuf)
preserves sl.Bytes(ubuf, 0, len(ubuf))
ensures   Mem(ubuf) && b.Mem()                // was: only on err == nil
ensures   sl.Bytes(b.UBuf(), 0, len(b.UBuf()))
ensures   err != nil ==> err.ErrorMem()
```

* Conditioning `FixLengths` on `ubuf == nil` protects all decoded-mode
  callers/proofs (nothing changes for them) while permitting exactly the
  fresh-layer case. Implementations must now verify their `FixLengths`
  behavior only under serialize mode.
* The unconditional `Mem`/`b.Mem()` in the post is provable for `SCMP` and
  the message types as-is (their bodies already re-fold on all error paths);
  `Payload` and `layers.BFD` are trusted stubs to adjust textually.
* `(*SCION).SerializeTo` (`scion.go:212-228`) gets a mode-split spec:
  `ubuf != nil ==> acc(s.Mem(ubuf), R0)` (as today) and
  `ubuf == nil ==> s.Mem(nil)` (full — the `FixLengths` branch writes
  `HdrLen`/`PayloadLen`). The body needs:
  * `pathSlice := ubuf == nil ? nil : ubuf[startP:endP]` ghost branching
    for the `Path.Len`/`Path.SerializeTo` calls (both already fine with
    `nil`, §3.1);
  * a serialize-mode variant of `SerializeAddrHdr`'s spec (address bytes
    from the predicate instead of `ubuf`);
  * verification of the `FixLengths` branch: the field writes need the
    full-permission serialize-mode `Mem` (above); the `uint8`/`uint16`
    casts produce no obligations since CI disables overflow checking
    (`overflow: '0'`), and serialize mode leaves `HdrLen`/`PayloadLen`
    unconstrained, so no buffer-size bound is required;
  * the new IO postcondition (§4.6).

### 4.5 The trusted `SerializeLayers` spec

Since the call must stay, `writer.gobra:105-112` gets a real (trusted)
quantified specification. Sketch:

```gobra
requires  len(layerBufs) == len(layers)
requires  w != nil && w.Mem()
requires  sl.Bytes(w.UBuf(), 0, len(w.UBuf()))
requires  opts.FixLengths ==> forall i int :: { &layers[i] } 0 <= i && i < len(layers) ==>
              layerBufs[i] == nil                       // cf. §4.4
requires  forall i, j int :: { &layers[i], &layers[j] } 0 <= i && i < j && j < len(layers) ==>
              layers[i] !== layers[j]                    // injectivity, cf. decodeLayers
requires  acc(layerBufs, R20)
requires  forall i int :: { &layers[i] } 0 <= i && i < len(layers) ==>
              (acc(&layers[i], R20) && layers[i] != nil && layers[i].Mem(layerBufs[i]))
requires  forall i int :: { &layers[i] } 0 <= i && i < len(layers) ==>
              sl.Bytes(layerBufs[i], 0, len(layerBufs[i]))
ensures   w.Mem() && sl.Bytes(w.UBuf(), 0, len(w.UBuf()))
ensures   acc(layerBufs, R20)
ensures   forall i int :: { &layers[i] } 0 <= i && i < len(layers) ==>
              (acc(&layers[i], R20) && layers[i].Mem(layerBufs[i]) &&
               sl.Bytes(layerBufs[i], 0, len(layerBufs[i])))       // also on error, cf. §4.4
ensures   err != nil ==> err.ErrorMem()
ensures   err == nil && 0 < len(layers) ==> /* IO clause, §4.6 */
```

Notes:

* In `prepareSCMP`, `layerBufs` becomes a real ghost sequence built
  alongside `scmpLayers` — `[nil, nil, nil]`, extended with `quote` in the
  `cause != nil` branch — replacing today's `nil` placeholder at
  `dataplane.go:5118`.
* Three layers share the buffer `nil`, so the quantified
  `sl.Bytes(layerBufs[i], 0, 0)` demands three instances of
  `sl.Bytes(nil, 0, 0)`. That is fine: the predicate body quantifies over
  zero locations, so arbitrarily many full instances can be folded
  (precedent: `fold sl.Bytes(nil, 0, 0)` in `packSCMP`,
  `dataplane.go:2206`).
* The spec is justified against the (unverified) gopacket implementation:
  it calls `w.Clear()` and then `layers[i].SerializeTo(w, opts)` from last
  to first, returning on the first error; with the strengthened interface
  postconditions of §4.4 (unconditional `Mem`), every quantified resource
  is restored on both success and failure. The `PushLayer` bookkeeping it
  also performs is unobservable to the router (`Layers()` is
  `requires false` and never called).
* Since *all four* layers — including `&scionL` — are now dispatched
  through the `SerializableLayer` interface, everything
  `(*SCION).SerializeTo` needs must fit through the interface footprint:
  full `Mem(ubuf)` (which the interface provides) plus
  `sl.Bytes(ubuf, ...)`. This is precisely why the serialize-mode
  `SCION.Mem(nil)` (§4.2/§4.3) must be *self-contained* (path resources,
  address bytes, field permissions all inside), and `*SCION` must keep
  satisfying the (relaxed) interface via its mode-split implementation
  spec.

### 4.6 Deriving `!IsSupportedPkt(result)` through the interface

This is the delicate part under the no-code-change constraint: the fact
"byte 4 of the output is `L4SCMP`" must flow from `(*SCION).SerializeTo`
through two abstraction boundaries that cannot name SCION concepts —
the `SerializableLayer` interface and the generic `SerializeLayers` spec
(`gopacket` cannot import `slayers`). The route:

1. **A gopacket-level twin of `IsSupportedRawPkt`.** Define in the
   `gopacket` stubs a ghost, opaque
   `pure func IsSupportedRawPkt(raw seq[byte]) bool` with the same body as
   `slayers.IsSupportedRawPkt` (`scion_spec.gobra:514-520`) — it only
   reads `raw[4]`/`raw[8]` against numeric constants, so no `slayers`
   import is needed — plus a one-line bridging lemma in `slayers`
   (`reveal` both) equating the two.
2. **An abstraction hook on the interface.** Extend `SerializableLayer`
   with a ghost pure method, e.g.

   ```gobra
   ghost
   requires acc(Mem(ubuf), _)
   decreases
   pure SerializesToSupportedPkt(ghost ubuf []byte) bool
   ```

   with the documented meaning "if this layer serializes *outermost*, the
   resulting packet is supported". Implementations:
   `*SCION` returns, in serialize mode (`ubuf == nil`),
   `s.PathType == scion.PathType && s.NextHdr != L4SCMP` over its fields,
   and in decoded mode `IsSupportedPkt(ubuf)`; the SCMP message types,
   `Payload`, and the BFD stub return `false` (they never serialize
   outermost in verified code — see the caveat below).
3. **Interface postconditions on `SerializeTo`**:
   * *stability*: `err == nil ==> SerializesToSupportedPkt(ubuf) ==
     old(SerializesToSupportedPkt(ubuf))` — provable for `*SCION` because
     serialization never writes `NextHdr`/`PathType` (the `FixLengths`
     branch only writes `HdrLen`/`PayloadLen`); trivial for layers with a
     constant hook. Without this clause the hook's value would be unknown
     after the call (the caller only gets `Mem(ubuf)` back, not field
     equalities).
   * *on `*SCION` only* (implementation spec, used for the implementation
     proof): `err == nil ==> gopacket.IsSupportedRawPkt(b.View()) ==
     SerializesToSupportedPkt(ubuf)`. This is provable in the body: the
     common-header write (`buf[4] = uint8(s.NextHdr)`,
     `buf[8] = uint8(s.PathType)`, `scion.go:258-262`) determines exactly
     the two inspected bytes, and the later
     `SerializeAddrHdr`/`Path.SerializeTo` calls only touch offsets
     ≥ `CmnHdrLen` (the existing `IsSupportedPktSubslice` machinery,
     `scion_spec.gobra:522-534`, and the serialize-mode analog of
     `IsSupportedPktLemma`, `scion.go:267-270`, frame this).
4. **Forwarding through `SerializeLayers`** (trusted):

   ```gobra
   ensures err == nil && 0 < len(layers) ==>
       IsSupportedRawPkt(w.View()) == layers[0].SerializesToSupportedPkt(layerBufs[0])
   ```

   Justification: the implementation serializes `layers[0]` *last*, so the
   buffer state at that call's return is the final state, and for the
   network-header layer the clause is exactly its per-implementation
   postcondition from step 3. **Caveat**: as stated, the trusted clause
   asserts this for *any* first layer, including ones (e.g. `Payload`)
   whose hook cannot truthfully describe the final bytes. Since the spec
   is trusted either way, this is a documented soundness assumption
   ("only meaningful when `layers[0]` is the outermost network-header
   layer"); it can be made self-guarding by adding a second hook
   (`ghost pure IsNetworkHeaderLayer() bool`, `true` only for `*SCION`)
   and conditioning the clause on it.
5. **Back in `prepareSCMP`**: `scionL.NextHdr == L4SCMP` (set at
   `dataplane.go:5085`, stable by step 3) makes the hook `false`, so
   `!gopacket.IsSupportedRawPkt(p.buffer.View())`; the bridging lemma and
   a small `View`/`UBuf` lemma
   (`View() == seqs.ToSeqByte(UBuf())`, `writer.gobra:48-54`; both
   functions read bytes 4 and 8) yield
   `!slayers.IsSupportedPkt(p.buffer.UBuf())`, and `Bytes()`
   (`writer.gobra:56-59`) gives `result === p.buffer.UBuf()` — closing
   postcondition `dataplane.go:4917-4918`. This mirrors the pattern in
   `updateSCIONLayer` (`dataplane.go:4784-4789`), sourced from field
   values instead of `old(IsSupportedPkt(rawPkt))`.

---

## 5. Changes to `prepareSCMP` / `packSCMP` and call sites

* **Preconditions to add** (`prepareSCMP`, and threaded through
  `packSCMP` + its ~9 call sites):
  * `scmpP != nil && scmpP.Mem(nil)` — foldable at each construction site,
    where the literal's field permissions are freshly available (e.g.
    `dataplane.go:2422`); with §4.1 this is a one-line `fold` per site.
  * `acc(&p.rawPkt, R55)` and the relation between `p.rawPkt` and `ub`
    (they are the same slice in all callers) so the quote's
    `Payload.Mem(quote)`/`sl.Bytes(quote, ...)` can be carved out of
    `sl.Bytes(ub, ...)` and recombined afterwards.
* **Proof work in the body (post-`TODO()` region)**:
  1. re-fold `revPath.Mem(rawPath)` → `revPath.Mem(nil)`;
  2. fold serialize-mode `scionL.Mem(nil)` after the field assignments and
     `Set{Dst,Src}Addr` calls (the `SetSrcAddr` ghost argument flipped to
     wildcard mode and the `SetDstAddr`/`SetSrcAddr` postconditions
     strengthened per §4.3); fold `ChecksumMem(scionL)` and then
     `scmpH.Mem(nil)` after `SetNetworkLayerForChecksum`;
  3. discharge the `hdrLen` computation (`AddrHdrLen(nil, ...)`,
     `Path.Len(nil)` through pure helper functions over `Mem(nil)`);
  4. build the ghost `layerBufs` sequence alongside `scmpLayers`
     (`[nil, nil, nil]`, plus `quote` in the `cause != nil` branch) and
     invoke `SerializeLayers` against the new trusted spec (§4.5); all
     predicates come back on both success and error paths thanks to the
     strengthened error postconditions (§4.4);
  5. at the end: unfold the fresh layers' predicates (they die with the
     function), apply the `SrcAddr()` magic wand, recombine all `ub`
     ranges to return `sl.Bytes(ub, 0, len(ub))` and
     `acc(p.scionLayer.Mem(ub), R4)`;
  6. fold `ErrorMem` for `scmpError{...}` and conclude the
     `!IsSupportedPkt(result)` post per §4.6.

---

## 6. Milestones

Ordered so that each step keeps CI green (`pkg/slayers` ≈ 25 min,
`pkg/slayers/path/scion` ≈ 30 min, `router` ≈ up to 6 h per CI run —
budget accordingly; perf regressions in `dataplane.go` are a real risk).

1. **M1 — `BaseLayer.Mem` nil-mode** (§4.1) + adapt `SCMP`/message-type
   proofs and `LayerPayload` specs. Small/medium; contained in
   `pkg/slayers`.
   **Status: implemented on this branch** (pending a CI/Gobra run):
   * `BaseLayer.Mem` fresh mode, with `Contents == nil && Payload == nil`
     in the `ub == nil` branch so the `gopacket.Layer` interface's
     `LayerPayload` contract stays satisfiable;
   * `extnBase.Mem` additionally pins `ActualLen == 0` in fresh mode,
     preserving every fact the old definition yielded for a nil buffer;
   * all `LayerPayload` specs over `BaseLayer` (SCMP, the 7 SCMP messages,
     both extensions and both skippers, and `BaseLayer.LayerPayload`
     itself) conditionalized on `ub != nil`;
   * `FoldFreshMem` witness lemmas for `SCMP` and all 7 message types —
     the machine-checked form of §1.2's positive experiments;
   * `DecodeFromBytes` of `SCMP` + the 7 message types now ensure their
     minimum length on success, so decoded-mode call sites (e.g. the
     traceroute handler's unfolds, `router/dataplane.go:4100-4120`) can
     derive `data != nil` and keep using the aliasing facts;
   * §4.6 step 1 done early (it is additive): `gopacket.IsSupportedRawPkt`
     twin + `slayers.IsSupportedRawPktEqGopacket` bridging lemma.
2. **M2 — serialize-mode `*SCION.Mem`** (§4.2) + `ChecksumMem`
   re-fractioning, the asymmetric address-byte amounts, and the
   `SetDstAddr`/`SetSrcAddr` postcondition strengthening (§4.3). Medium;
   touches many `SCION` lemmas' guards (`ub != nil`). Start with a smoke
   test that a wildcard conjunct inside a predicate body folds/unfolds as
   expected.
3. **M3 — `(*SCION).SerializeTo`**: mode-split spec, `SerializeAddrHdr`
   serialize-mode, verify the `FixLengths` branch, prove the
   hook postcondition of §4.6 (step 3). This is the hardest single item.
   Large.
4. **M4 — interface + `SerializeLayers` spec updates** in `writer.gobra`
   (§4.4, §4.5, §4.6 steps 1–2, 4): relax `FixLengths`, strengthen error
   postconditions, add the ghost hook, the gopacket-level
   `IsSupportedRawPkt` twin + bridging lemma, and the quantified trusted
   `SerializeLayers` spec; re-verify the closed set of implementers;
   adjust the `Payload`/`BFD` trusted stubs. Medium.
   **Status: partially implemented on this branch** (pending a CI/Gobra
   run): the error-case postconditions of `SerializableLayer.SerializeTo`
   and all implementations (`SCMP` + the 7 message types re-fold `Mem`
   before every error return, so their strengthened specs remain provable;
   `Payload`/`BFD` stubs adjusted textually; `SCION` was already
   unconditional), plus the `IsSupportedRawPkt` twin + bridging lemma.
   Deliberately *not* yet done: the `FixLengths` relaxation (it would
   break `*SCION`'s implementation proof until M3 verifies the
   `FixLengths` branch), the ghost hook, and the `SerializeLayers` spec.
5. **M5 — `prepareSCMP` itself** (§5): spec extensions, call-site folds,
   ghost `layerBufs`, drop the `TODO()`. Large, but mostly mechanical once
   M1–M4 are in; expect iteration on router CI time.
6. **M6 — cleanup**: remove `Unreachable()` from the `FixLengths` branch,
   revisit `bfdSend` (§8), document the serialize-mode idiom.

## 7. Risks / open points

* **Verification time** of `dataplane.go` (already the 6 h/`chop 10`
  package). Mitigate with `outline(...)` blocks and `opaque` helper
  functions for the new fold-heavy regions.
* **Wildcard permission amounts inside predicate bodies** (§4.3) and
  wildcard-mode folds of `net.IPAddr.Mem()` are less-trodden Gobra
  territory; validate with a small experiment before building M2 on them.
  Fallback: keep the `RawSrcAddr` bytes *outside* the predicates entirely
  and weaken `SerializeAddrHdr`/`computeChecksum`'s specs to take them as
  separate wildcard clauses — workable because those specs are on concrete
  methods, but it makes the serialize-mode `SCION.Mem` non-self-contained,
  which conflicts with interface dispatch (§4.5); in that case the src
  bytes would have to ride in a second, `slayers`-internal predicate
  referenced from `Mem`'s serialize branch.
* **Gobra interface-implementation proofs** with mode-split permission
  amounts (`ubuf == nil ? full : R0`) and ghost pure interface methods are
  unusual; unlike in a design where the SCION call is concrete, `*SCION`
  **must** remain a `SerializableLayer` implementer here, so brittleness
  in the implementation proof has no cheap fallback — prototype early
  (M4 before M3 completion is fine, the two are independent).
* **The trusted `SerializeLayers` IO clause** (§4.6 step 4) is a genuine
  (if small) soundness assumption about which layer is outermost; gate it
  with the `IsNetworkHeaderLayer()` hook to keep it honest.
* **`SrcAddr()`/`SetDstAddr` aliasing**: the `RawDstAddr` fraction
  originates from `acc(p.scionLayer.Mem(ub), R4)`-governed memory via a
  magic wand; getting the fraction arithmetic right (so that the wand can
  be applied at exit) needs care, but has precedent (`addEndhostPort`,
  `dataplane.go:4734-4755`).

## 8. Side benefit

The same serialize-mode machinery is exactly what
`newBFDSend`/`bfdSend.Send` (`dataplane.go:4817-4898`, currently
`trusted` / `requires false`) need: fresh `SCION` layer, `FixLengths: true`,
`SerializeLayers` with a fresh `layers.BFD`. M1–M4 unlock that verification
almost for free (the BFD layer's spec is a trusted stub in
`verification/dependencies`), with `empty.Path`/`onehop.Path` (both already
`Mem(nil)`-friendly or buffer-light) instead of `scion.Decoded`.
