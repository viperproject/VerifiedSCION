# Disabling non-linear arithmetic (`--disableNL`)

**Question.** Does VerifiedSCION still verify if we switch off Gobra's non-linear
arithmetic entirely?

**Answer.** No. 17 of the 20 verification jobs in `.github/workflows/gobra.yml`
pass unchanged, but three fail with 15 errors in total. Every one of those errors
comes from Viper's *permission* algebra, not from the integer arithmetic of the
SCION proofs.

## How to reproduce

Append `--disableNL` to `default_job_cfg.other` in `gobra-mod.json`; it is
inherited by every package, since no `gobra.json` overrides it (job-level config
is merged with `orElse` over the module-level one). Then run each job as CI does:

```sh
java -Xss1g -Xmx4g -jar gobra.jar --config <package>
```

The numbers below were produced with Gobra `d5f487c` and Z3 4.8.7 (the version
the CI image pins), on a 4-vCPU/15 GB machine comparable to a GitHub runner,
against VerifiedSCION `7f39fa4`. Jobs were run sequentially; timings are single
samples and should be read as indicative.

## Results

| job | baseline | `--disableNL` |
| --- | --- | --- |
| `verification` (recursive) | PASS 121s | **FAIL — 1 error** |
| `verification/dependencies/.../gopacket/layers` | PASS | PASS |
| `pkg/addr` | PASS | PASS |
| `pkg/experimental/epic` | PASS | PASS |
| `pkg/log` | PASS | PASS |
| `pkg/private/serrors` | PASS | PASS |
| `pkg/scrypto` | PASS | PASS |
| `pkg/slayers` | PASS 186s | PASS 188s |
| `pkg/slayers/path` | PASS 60s | PASS 58s |
| `pkg/slayers/path/empty` | PASS 33s | PASS 34s |
| `pkg/slayers/path/epic` | PASS 53s | PASS 52s |
| `pkg/slayers/path/onehop` | PASS 50s | PASS 49s |
| `pkg/slayers/path/scion` | PASS 306s | PASS 313s |
| `private/topology` | PASS | PASS |
| `private/topology/underlay` | PASS | PASS |
| `private/underlay/conn` | PASS 44s | **FAIL — 6 errors** |
| `private/underlay/sockctrl` | PASS | PASS |
| `router/bfd` | PASS | PASS |
| `router/control` | PASS | PASS |
| `router` | PASS 4157s | **FAIL — 8 errors, 1264s** |

### The 15 errors

All of them are "might not suffice" on a resource held with a wildcard:

- `verification/utils/monoset/monoset.gobra:79` — `unfold acc(b.Contains(i), _)`
  in `PromoteContains`; `Contains` holds `acc(b.valuesMap[i], _)`.
- `private/underlay/conn/conn_spec.gobra:80,97,115,166,183,201` — all six are
  `fold acc(c.connUDPBase.Mem(), _)`; `Mem`/`MemWithoutConn` hold
  `acc(c.Listen.Mem(), _)` and `acc(c.Remote.Mem(), _)`.
- `router/dataplane.go:1766,1837,2800,3712,4439,4609` and
  `router/dataplane_spec.gobra:128,374` — wildcard folds/unfolds of `d.Mem()`,
  `accBatchConn`, `accAddr`, `forwardingMetricsInv`, `macFactoryInv`, and calls
  whose preconditions need `acc(..., _)`.

## Root cause

Folding or unfolding a predicate held with amount `p` scales every `acc(x.f, q)`
in its body to `PermTimes(q, p)` (`rules/Producer.scala`, `rules/Consumer.scala`).
So:

- `q` a literal, `p` symbolic gives `1/2 * w` — linear, unaffected.
- `q` and `p` both wildcards gives `w1 * w2` — a product of two symbolic
  variables.

The trigger is therefore *nested* wildcards specifically: holding `acc(P(), _)`
where `P`'s body itself contains `acc(..., _)`. This 12-line Viper file, the
shape of `monoset.PromoteContains`, reproduces the whole thing — it verifies
normally and fails under `--disableNL`:

```viper
field f: Int
predicate P(x: Ref) { acc(x.f, wildcard) }

method promote(x: Ref)
  requires acc(P(x), wildcard)
  ensures  acc(P(x))
{ unfold acc(P(x), wildcard); fold acc(P(x)) }
```

`--proverLogFile` shows the goal that flips, and there is no integer in it:

```smt2
(assert ($Perm.isReadVar $k@5@04))                       ; k5 >= 0 /\ k5 != 0
(assert ($Perm.isReadVar $k@6@04))                       ; k6 >= 0 /\ k6 != 0
(assert (<= $Perm.No (* $k@6@04 $k@5@04)))
(assert (<= (* $k@6@04 $k@5@04) $Perm.Write))
(assert (not (not (= (* $k@6@04 $k@5@04) $Perm.No))))    ; refute k6*k5 = 0
(check-sat)
```

Replaying that script gives `unsat` with `smt.arith.nl=true` and `unknown` with
`smt.arith.nl=false`.

Note that "non-linear *integer* arithmetic", as both Gobra's and Silicon's help
texts put it, is a misnomer. `--disableNL` emits `(set-option :smt.arith.nl
false)`, which Z3 documents as "(incomplete) nonlinear arithmetic support based
on Groebner basis and interval propagation" — a switch on the arithmetic solver
as a whole, with no sort restriction. Silicon declares `(define-sort $Perm ()
Real)`, so wildcard products are non-linear *real* arithmetic and fall under the
same switch. Z3 does not lose product reasoning outright: posed standalone, the
goal above is still discharged by cheap sign propagation. What it loses is the
systematic machinery, so in a full query context it no longer finds the proof.

## Mitigations evaluated

### Rewrite the specs to avoid nested wildcards — does not work as-is

Replacing the nested wildcards in `connUDPBase.Mem()`/`MemWithoutConn()` with a
fixed fraction (`R55`) removes all 6 original errors and introduces 3 new ones:

- `conn.go:431,440` — `LocalAddr`/`RemoteAddr` `unfold acc(c.MemWithoutConn(),
  R16)`, `defer fold`, and still `ensures u != nil ==> acc(u.Mem(), _)`. Handing
  a copy out *and* folding back works only because the inner wildcard makes the
  resource duplicable; a fixed fraction is consumed by the re-fold.
- `conn.go:391` — `fold cc.Mem()` at construction, where `laddr.Mem()` arrives as
  a wildcard from the caller and cannot yield a fixed `R55`.

The nested wildcard encodes "duplicable, no accounting". Substituting a constant
moves the obligation to the producer side, and fixing that propagates outward
through every caller.

### Silicon's `--unsafeWildcardOptimization`

`WildcardSimplifyingPermTimes` (`state/Terms.scala`) rewrites `w1 * w2` to
whichever variable has the smaller id and `w * literal` to `w`, so no product
reaches Z3. It keeps exact arithmetic for locations mentioned under `perm(loc)`
(`DefaultMainVerifier.scala`); VerifiedSCION has no Viper-level `perm(loc)` in
its specs, so the unsafe case appears inapplicable here.

### Permission-product axioms in Silicon's preamble

The products only need positivity and monotonicity, which can be stated as
quantified assertions and matched on `(* p1 p2)` even with the NL solver off:

```smt2
(assert (forall ((p1 $Perm) (p2 $Perm)) (!
    (=> (and (< $Perm.No p1) (< $Perm.No p2)) (< $Perm.No (* p1 p2)))
    :pattern ((* p1 p2)) :qid |perm-times-pos|)))
```

plus `(* p1 p2) <= p2` when `p1 <= 1`, and the symmetric variant. Unlike the
option above this is sound rather than an approximation, and costs nothing when
NL is on. It would belong upstream in Silicon, gated on `disableNL`.

Both mitigations fix the two smaller jobs under `--disableNL`, and
`unsafeWildcardOptimization` fixes `router` as well, so the approach is not
limited to small proofs:

| job | `--disableNL` | + `unsafeWildcardOptimization` | + preamble axioms |
| --- | --- | --- | --- |
| `private/underlay/conn` | FAIL (6) | PASS 40s | PASS 32s |
| `verification` | FAIL (1) | PASS 98s | PASS 85s |
| `router` | FAIL (8) | PASS 4442s | not measured |

## Performance

Disabling NL neither breaks nor speeds up the `slayers` tree. Sequential runs on
an idle machine, single sample each:

| package | baseline | `--disableNL` | + `unsafeWildcardOpt` | + axioms |
| --- | --- | --- | --- | --- |
| `pkg/slayers` | 186s | 188s | 187s | 179s |
| `pkg/slayers/path` | 60s | 58s | 58s | 61s |
| `pkg/slayers/path/empty` | 33s | 34s | 33s | 31s |
| `pkg/slayers/path/epic` | 53s | 52s | 54s | 54s |
| `pkg/slayers/path/onehop` | 50s | 49s | 50s | 50s |
| `pkg/slayers/path/scion` | 306s | 313s | 273s | 295s |
| **total** | **688s** | **694s** | **655s** | **670s** |

All cells pass. The spread is within single-sample noise on this machine.

The router tells the same story. Switching non-linear arithmetic off does not
make it cheaper -- the one configuration that both verifies and disables NL is
slightly more expensive than what CI runs today:

| router config | result | time |
| --- | --- | --- |
| current (NL on) | PASS | 4157s |
| `--disableNL` | FAIL, 8 errors | 1264s (abandons members after the first error) |
| `--disableNL --unsafeWildcardOptimization` | PASS | 4442s |

Single samples, so +285s is better read as "no faster, perhaps a few percent
slower" than as a precise figure. Either way there is no performance argument
for disabling NL; the reasons to want it would be determinism or a stricter
prover configuration.

The run is also badly tail-bound: 9 of the 10 chop tasks finish in the first
~20 minutes and one task accounts for the rest, in both configurations.

## Adopted configuration

The 17 jobs that pass now opt in individually, through a `gobra.json` next to the
package:

```json
{
  "other": ["--disableNL"]
}
```

`verification`, `private/underlay/conn` and `router` deliberately have no such
entry and keep non-linear arithmetic.

Opting in per package, rather than setting the flag once in `gobra-mod.json` and
exempting the three, is forced by how the option is defined. `disableNL` is an
`opt[Boolean]` with no `--nodisableNL` counterpart, and it is folded in with
`disableNL || input.disableNL.value.contains(true)`, so once the module config
sets it no job can clear it. The merge itself would allow an override — job and
module configs are combined field-wise with `orElse`, and `toInputConfigOption`
records a value only when the option `isSupplied`, which is also why a job
`other` list does not disturb the module-level options it omits — but there is
no way to *supply* `false`.

A structured `disable_nl: Option[Boolean]` field in `VerificationJobCfg` would
remove that restriction and shrink this to four files: one `true` in
`gobra-mod.json` and three `false` overrides. That is a Gobra change, so it
cannot land here first.
