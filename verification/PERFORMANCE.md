# Where the router's verification time goes

`router/` is by far the most expensive package to verify: the CI gives it a six
hour budget, while every other package gets between five and thirty minutes.
Most of that budget is consumed by a handful of members. This note records how
the cost is distributed, what was measured, and which changes are likely to pay
off, so that the next person to look at this does not have to rediscover it.

Everything below was measured with `verification/scripts/verify-member.py`,
which verifies **one member at a time** using Gobra's isolation
(`-i router/dataplane.go@<line>`, after which the chopper keeps only the slice
of the program that the member needs) and the options that the CI uses. Numbers
are wall clock for the whole Gobra run on a 4-core machine; roughly 140 s of
each of them is Gobra's front end, which the isolated runs cannot avoid.

## Cost per member

| member | isolated run | of which: the contract alone |
|---|---|---|
| `Run` itself, for reference | 2.8 min | — |
| `processOHP` | 5.5 min | — |
| `processPkt` | 5.7 min | — |
| `doXover` | 12 min | 6 min |
| the `rc` closure of `Run` (`closureCall$rc_Run…`) | 26 min | 2.5 min |
| `process` | 109 min | 4 min |

The "contract alone" column comes from cutting the body at its first statement
(see below): it is what the run still costs when the member has no body left.
Since the front end alone is ~2.5 min, `Run` and `processPkt`/`processOHP` are
in fact only a couple of minutes of solving each; the cost is concentrated in
`process`, in the `rc` closure and, to a lesser extent, in `doXover`. That `Run`
itself is cheap while the closure it declares is not is expected: `Run`'s body
is broken up by seven `outline` blocks, and the packet loop lives in `rc`.

## The backend options are not the problem

Every deviation from what `router/gobra.json` already asks for made things
worse, so the slowness is not a misconfiguration:

| change | effect |
|---|---|
| `mce_mode: "od"` instead of `"on"` (the module default) | `processOHP` still running when the baseline had finished |
| `#backend[moreJoins()]` on `doXover`, i.e. join every branch | more than twice as slow |
| `#backend[moreJoins()]` on `process` | ≥ 8446 s against a 7737 s baseline under the same load |
| `#backend[exhaleModeQP(2)]` on `doXover` | no improvement |

Joining is the interesting one, because the profile below says `process` explores
its whole tail once per side of the `IsXover` branch. Joining does remove that
duplication — and still loses, because merging two copies of a heap this
fragmented costs more than exploring it twice.

`mce_mode: "on"` in particular is not a leftover: with on-demand exhale, Silicon
first tries a greedy exhale and only retries with the complete one when that
fails. In this package the greedy attempt fails often enough that the retries
cost more than always being complete. Note also that Gobra never passes
`--exhaleModeQP`, and Silicon's default for it is the complete mode regardless
of `--exhaleMode`, so quantified permissions are always exhaled completely.

## Where the time goes inside a member

The body of a member can be cut short by inserting `TODO()` (which is
`ensures false`), making everything after the cut unreachable. Timing a sequence
of cuts gives a profile of the member. For `doXover`:

| what runs | s |
|---|---|
| nothing (contract only) | 351 |
| … up to the range splits and `XoverLemma` | 417 |
| … up to and including `IncPath` | 465 |
| … including the block of 14 assertions | 464 |
| … including both hop/info field decodings | 458 |
| the whole body, without the final `return` | 566 |
| the whole member | 707 |

And for `process`:

| what runs | s |
|---|---|
| nothing (contract only) | 237 |
| … `parsePath` | 307 |
| … the next four validators | 446 |
| … `verifyCurrentMAC`, `handleIngressRouterAlert` | 487 |
| … the whole inbound branch, `InternalEnterEvent` included | 630 |
| … the whole xover branch, `doXover` included | 1319 |
| the whole member | 6548 |

Four fifths of `process` is therefore in its last 130 lines: `validateEgressUp`,
`egressInterface`, the two egress branches with their IO-spec events, the three
`reveal PktUpdate(…)`/`reveal absIO_val(…)`, and the three exits. That tail sits
after the `if p.path.IsXover(…)` branch, which *rejoins*; since `more_joins:
"impure"` does not join `if` statements, everything in the tail is explored once
per side of that branch, and again per side of each `ghost if
slayers.IsSupportedPkt(ub)` and `ghost if !p.segmentChange` inside it.

Back to `doXover`: two things stand out. The block of assertions in the middle
and the two field decodings are free — the facts they restate are already in the path condition.
And after subtracting the front end, roughly 60 % of the remaining time is spent
on `doXover`'s *own contract*: ~210 s proving that its 26 `ensures` clauses are
well defined before the body starts, and at least ~140 s exhaling them at the
single successful exit. Dropping any one clause changes little (removing the
largest one saves 4 %); the cost is spread evenly over clauses that each mention
`absPkt(ub)` or `old(absPkt(ub))` and therefore drag in
`CurrSeg`/`LeftSeg`/`MidSeg`/`RightSeg` → `segment` → the recursive `hopFields`,
all of which have to be framed against the current `sl.Bytes(ub, …)` snapshot.

`process` is expensive for the opposite reason: its contract costs about 100 s
of solver time out of 109 minutes. Its body calls seventeen methods whose
specifications total
**568 clauses**, each of which is exhaled and then inhaled again over a heap
that holds `p.scionLayer.Mem(ub)`, a fragmented `sl.Bytes(ub, …)` and the
`absPkt(ub)` function stack. Nine of those callees share eleven *literally
identical* clauses (permission to `p.d`, `p.path`, `p.buffer`,
`p.buffer.UBuf()`, `p.lastLayer`, and `p.d.validResult`).

The `rc` closure has no postcondition at all, and cutting its body away brings
its run down to the front end alone (152 s): all 26 minutes are the two
nested loops, whose invariants carry quantified assertions over the 64-message
batch — including `forall i :: MsgToAbsVal(&msgs[i], ingressID) == ioValSeq[i]`,
which unfolds the whole packet abstraction for every message — and are
re-established on every iteration.

## Contributing factors

* **Permission fragmentation.** `p.scionLayer.Mem(..)` is used at 18 distinct
  permission amounts in `dataplane.go`, `p.scionLayer.Path.Mem(..)` at 11,
  `d.Mem(..)` at 8. There are 136 calls to the `sl.*_Bytes` split/combine
  lemmas at 11 distinct amounts. Each of them folds or unfolds a predicate whose
  body is a quantified `forall i :: acc(&s[i])`, so each creates or consumes
  quantified-permission chunks. Under the complete exhale that this package
  needs, every subsequent heap lookup summarises all of them.
* **Branches are not joined.** `more_joins: "impure"` only joins impure
  conditionals inside assertions; `if` statements are only joined under
  `moreJoins(all)`, which `Run` and `rc` opt into and the others do not. So
  `process`'s seventeen error exits each exhale its postcondition (25 `ensures`
  plus 11 `preserves`, so 36 clauses once encoded) separately, and — far more
  expensive — its whole tail is explored once per side of the `IsXover` branch
  that precedes it. Joining is not a free win: on `doXover` it was more than
  twice as slow.
* **`old(...)` in leaf contracts.** The contracts of the members that `process`
  calls contain 61 `old(...)` applications and 88 applications of `absPkt`,
  which forces Silicon to keep querying the pre-state heap as well.

## What was tried, and did not work

Rewriting the specifications locally does not help either. Each of these was
implemented, verified (0 errors) and timed:

| change | result |
|---|---|
| delete the assertions `doXover` repeats (`p.path === …GetScionPath(ub)` 6×, `…GetBase(ubScionPath) == nextBase` 5×) | no change; the profile says they were already free |
| replace `doXover`'s eight repeated `ghost if typeOf(…) == *epic.Path` by one local ghost boolean | 841 s against a 707 s solo baseline — worse |
| thread the abstract packet through ghost parameters in `doXover`, removing nine `absPkt(ub)` and five `old(absPkt(ub))` from its contract | 892 s vs 915 s in a fair A/B — a wash |
| give `XoverEvent` and `ExternalEnterOrExitEvent` the intermediate abstract packets as parameters, instead of writing `AbsUpdateNonConsDirIngressSegID(oldPkt, ingressID)` nine times and `AbsDoXover(…)` five times inside it | `process` 7537 s with the machine to itself, against a 6548 s baseline that shared it — no gain |

The last two are the informative failures. Silicon evaluates a heap-dependent
function once per heap snapshot, not once per mention, so collapsing repeated
applications buys nothing; what the contract costs is the *number of distinct
states* in which its clauses have to be framed, and the `unfolding`-heavy
accessors (`UBPath`, `UBScionPath`, `GetPath`, `GetScionPath`,
`ValidPathMetaData`, `EqAbsHeader`, …) that each open `p.scionLayer.Mem(ub)`
again.

Taken together with the backend options above: six interventions, none of which
moved the number. The cost is spread thinly over a very large number of
individually expensive queries, and it is the *size and fragmentation of the
symbolic state* that makes each of them expensive. Anything that leaves the
state alone — reordering clauses, naming subterms, deleting assertions, changing
how branches are explored — leaves the cost alone too.

A corollary worth keeping in mind before the next attempt: measure in pairs.
Several of the differences above are smaller than the effect of sharing the
machine with a second Gobra run (a second run inflates a `process` measurement
from 6548 s to 7737 s), so a variant timed on its own against a baseline timed
under load will look like a win that is not there.

## What is left to try

That points at the changes that make the state itself smaller. They are real
refactors rather than annotations, which is why they were not attempted here.

1. **Bundle the resource footprint that the validators share into a predicate.**
   The eleven clauses common to nine of `process`'s callees — permission to
   `p.d`, `p.path`, `p.buffer`, `p.buffer.UBuf()`, `p.lastLayer`, plus
   `p.d.validResult` and two impure implications about `p.lastLayer` — can
   become a single predicate that each of them `preserves` and unfolds only on
   the paths that build an SCMP reply. That replaces roughly 17 × 2 × 8 clause
   exchanges along `process`'s path by one predicate chunk in each direction.
   This is the transformation that #424 applied to `DataPlane.Mem()`, and it
   attacks the state size rather than the specification text.
2. **Bundle the per-message resources in `rc`'s loop invariants** in the same
   way, so that an iteration exchanges one predicate instead of six quantified
   assertions over the 64-message batch. This needs a range predicate with
   take/put lemmas, since the body still has to get at one message at a time.
3. **Reduce the number of distinct permission amounts.** `p.scionLayer.Mem(..)`
   is currently used at 18 of them, and the `unfold acc(P, 1-R55)` /
   `unfold acc(P, R55)` idiom exists only so that a pure function can be
   evaluated in between. Every extra fraction is another chunk for the complete
   exhale to summarise.
4. **Outline the branches of `process`.** `Run` uses seven `outline` blocks;
   `process` and `processPkt` use none. An outlined block is verified as its own
   Viper method, so the state that the rest of `process` carries past it is
   whatever the outline's contract says, not everything the branch touched.

## Reproducing

```sh
export GOBRA=/path/to/gobra.jar Z3_EXE=/path/to/z3
./verification/scripts/verify-member.py --list router          # member -> line
./verification/scripts/verify-member.py router doXover
./verification/scripts/verify-member.py router rc              # a closure of Run
```

Two Gobra limitations get in the way and are worth fixing upstream:

* Member isolation cannot be expressed in the JSON configuration that the CI now
  uses. `input_files` makes Gobra abort with
  `Logic error: the configuration mode should be one of file, package, recursive
  or config` (`InputConfig.fromVerificationJobCfg` fills in `input` but not
  `cutInputWithIdxs`, which is what `InputConfig.rawConfig` dispatches on), and
  `-i` inside `other` is rejected outright. Hence the script builds a full
  command line instead.
* `gobra --config router` from the repository root fails with
  `Could not find module configuration file gobra-mod.json …`, because the
  search for the module config walks `getParentFile()` on the *relative* path
  and stops immediately. An absolute path works.
