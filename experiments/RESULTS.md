# Encoding experiments

Four small, handwritten encodings in [Encodings.lean](Encodings.lean) compare
readability and proof work using the existing `maximum`, `countdown` and
`irreducible` C fixtures. There is no second translator, new dependency, or change
to the default output. All effectful variants reuse `GotoLean.Action` and its
existing execution and verification machinery.

| Example / encoding | Program lines | Proof + invariant lines |
| --- | ---: | ---: |
| Maximum / generated dispatcher | 27 | 25 |
| Maximum / direct Action | 2 | 6 |
| Countdown / generated dispatcher | 35 | 17 |
| Countdown / typed block arguments | 15 | 13 |
| Countdown / collapsed loop state | 3 | 10 |
| Countdown / native `while` | 8 | 6 |
| Irreducible graph / generated dispatcher | 59 | — |
| Irreducible graph / typed block arguments | 13 | — |

Counts exclude blank lines, comments, imports, namespace markers, and concrete
execution wrappers. Program counts include the types and entry definitions they
need. The direct-maximum proof count excludes its additional 15-line equivalence
proof. These are microexamples, not general code-size or performance benchmarks.
Handwritten variants also fold return tails and remove dead state, so the gains
cannot all be attributed to surface syntax alone.

## What worked

- Direct `Action` code makes an acyclic expression much easier to read and prove.
  `maximum_equiv` proves equivalence with the generated function for **every**
  postcondition, not just the maximum specification.
- Typed block constructors carry their live arguments. This removes the shared
  locals record and optional return slot, so the invariant no longer needs to
  rule out a missing return value. Named block functions work with the same
  trampoline even for the irreducible two-entry cycle.
- Combining a natural loop guard/body and its return tail removes the PC entirely
  for countdown. The existing unbounded safety rule still applies.
- Native Lean `while` gives the cleanest loop and shortest proof here. Its
  invariant and decreasing measure fit on two lines. The proof checks the
  decrease of the bitvector's unsigned value rather than assuming termination.

## Checks and limits

This opt-in experiment runs 621 comparisons against the generated programs: 36 maximum,
195 countdown across three encodings, and 390 irreducible-graph cases. The generated
programs already undergo the native C differential suite. Fuel is deliberately
ample; collapsing blocks changes the amount of fuel consumed. The maximum
postcondition equivalence is formal; loop/irreducible comparisons are concrete,
with separate functional proofs for countdown. There is no general CFG-rewriting
or translation-correctness theorem here.

Lean 4.35's intrinsic loop annotations needed `simp only [countdown]` before
`vcgen`; using `unfold countdown` instead produced an internal structural-equality
error about a let declaration. This is a reproducible tactic rough edge with a
one-line workaround. The checked proofs use only the usual Lean axioms.

## Recommendation

Keep one faithful generated representation for arbitrary GOTO input, including
explicit return blocks and declaration choices. Leave semantic simplification
to Lean: prove block invariants directly or write a small summary and prove its
equivalence, as `Direct.maximum_equiv` demonstrates. The smaller handwritten
examples do not justify adding control-flow optimization to the C++ printer.
No general Lean optimization pass is needed yet.

Native `while` is attractive for a later structured view, but it requires CFG
recovery, and this pure example does not solve nondeterminism, assertion outcomes,
or nontermination for a general GOTO program. The reduction in these examples
does not yet justify that machinery.

After the regular test suite has generated its imports, rerun directly with:

```sh
LEAN_PATH=build/tests lake env lean --run experiments/Encodings.lean
```
