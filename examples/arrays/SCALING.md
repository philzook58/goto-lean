# Scaling to more ACSL examples — 2026-10-22

Five more unchanged upstream entries translate: `fill`, `find`,
`is_sorted_until`, `rotate`, and `bubble_sort`. The pinned source revision is
unchanged; `upstream/SOURCE.json` includes hashes for their transitive headers and
ACSL files. No C++ printer, executable memory model, or generic checkpoint-rule
changes were needed.

## What is proved

| Entry | Generated lines | Handwritten proof lines | Universal Lean result |
|---|---:|---:|---|
| `fill` | 90 | 88 | Every element filled, byte frame preserved, safety and termination |
| `find` | 112 | 68 | First matching index or `n`, unchanged memory, safety and termination |
| `is_sorted_until` | 110 | 95 | Maximal sorted prefix, unchanged memory, safety and termination |
| `rotate` | 295, shared with reverse | 138 + shared helpers below | Rotated contents, return index, byte frame, safety and termination |
| `bubble_sort` | 229 | 310 | Signed ordering, permutation, byte frame, safety and termination |

The first three proofs quantify over every representable unsigned length and
32-bit element/key values, subject to explicit memory preconditions. Fill also
requires a nonwrapping array extent. The theorems are named `verify` in
`Proofs/Fill.lean`, `Proofs/Find.lean`, and `Proofs/IsSortedUntil.lean`. Each proves
`finishes` with its functional postcondition, so `GotoLean.finishes_run` also
supplies the original unbounded safety/partial-correctness specification.

Their conservative block bounds are `2*(n+2)` for fill and `4*(n+2)` for the two
scans. For these three proofs, the only shared additions are two unsigned index lemmas in
`Proofs/Array.lean`, totaling 16 lines including the namespace wrapper. The 251
lines of new algorithm proofs reuse the existing memory views and 54-line path
module. No additional tactic or proof-generation framework was introduced.

`is_sorted_until` proves the actual pairwise `Increasing` predicate and failure
of `Increasing` at the next element, not only a Boolean adjacent-order test.
A small local lemma proves that extending an increasing prefix by a sufficiently
large last element preserves pairwise order. The empty-array case is included.
All three theorem audits report only standard Lean axioms.

## Execution coverage

`scale.py` compares native C, generated Lean and independent Python results on
2,290 operation cases:

| Operation | Cases |
|---|---:|
| Fill | 765 |
| Find | 765 |
| Sorted-prefix scan | 153 |
| Rotation | 454 |
| Bubble sort | 153 |

Inputs include all arrays over `[-1,0,1]` through length four, plus random,
sorted, reverse-sorted and constant arrays through length 64, signed extrema,
absent keys, and empty/interior/end rotation pivots. Both runners check surrounding
sentinels; Lean also checks allocation extent and complete memory preservation
for read-only scans. Runner exhaustion and insufficient choices are failures.
These are concrete tests; the universal theorems are checked separately. The
sorting runner now uses the quadratic block bound from its completion theorem.

The original 860 search/reversal cases remain, making 3,150 case records across
the two comparison scripts. `make check` runs both scripts and the proof/axiom gates.

## Bounded symbolic checks and proof checking

CBMC 6.11.0 checks symbolic arrays with symbolic `n ≤ N`, complete unwinding,
bounds, pointers, signed overflow and division-by-zero checks. There is a
10-second limit per entry/bound. Sorting checks both order and occurrence counts
for every original value, including duplicates; rotation checks every element
against the original snapshot. Unused suffix elements are preserved.

| Entry | CBMC N=4 | CBMC N=8 | CBMC N=16 | Lean fresh proof-file check |
|---|---:|---:|---:|---:|
| Fill | 0.12 s | 0.22 s | 1.17 s | 0.54 s, all lengths |
| Find | 0.12 s | 0.17 s | 0.97 s | 0.99 s, all lengths |
| Sorted prefix | 0.12 s | 0.27 s | 0.72 s | 1.16 s, all lengths |
| Rotation | 0.67 s | 5.18 s | Timeout | 0.71 s, all lengths |
| Bubble sort | 1.37 s | Timeout | Timeout | 1.17 s, all lengths |

Every completed CBMC run verified its properties. Timeouts are inconclusive.
These single-run wall times are smoke measurements with built Lean imports;
they exclude proof construction and do not establish lower verification effort.
The sorting harness itself has nested counting loops, so its timeout cannot be
attributed solely to the sorting algorithm. No Frama-C/WP comparison was run.

Run `make benchmark-scale` to repeat these measurements. Complete logs and JSON
results are written under `.lake/`; `scale_cbmc.c` and `benchmark_scale.py` keep
the workload and time limits explicit.

## Reusing the reverse proof in rotation

`Proofs/Rotate.lean` now proves the original three-call program for every
representable `n` and pivot `k ≤ n`. The contract gives the exact rotated contents,
return value `n-k`, preservation of every byte outside the array, safety and
completion within `12*n+15` original interpreter blocks. The bound is conservative.
It assumes readable 32-bit elements and a nonwrapping 56-bit pointer-offset extent;
empty arrays and both endpoint pivots are included.

The key change is packaging: `Generated/Rotate.lean` already contains reverse,
rotate and swap in one body. `Entries/Reverse.lean` exposes reverse as an entry
into that same body. The existing reverse loop proof is checked against this
entry, and rotation uses its `Reverse.verify` contract three times. The old
`Generated.Reverse` module remains a one-line import for existing clients;
`make generate` no longer emits a second standalone reverse body. No source-level
inlining, duplicated loop proof, C++ folding or interpreter change was needed.
The proof is tied to this generated bundle; transporting it between independently
generated bundles with different activation types remains future work.

The reusable addition to the core is `GotoLean/CallSummary.lean` (46 lines).
`finishes_resume` attaches a caller continuation to a proved callee completion,
including arbitrary internal calls, outer stack frames and return checks.
The local `Proofs/Slices.lean` (102 lines) lifts a reversal of one subrange to the
whole array using the existing byte frame. Rotation itself takes 138 lines,
including the small arithmetic fact that three reversals implement rotation.
The reverse proof grows from 160 to 168 lines, chiefly to expose its existing
completion argument as a reusable contract. The entry view takes 34 lines.
These costs are explicit: modular reuse works, but this is not yet an automatic
or especially terse contract interface.

The table above records a fresh run after adding both proofs. Rotation
checks in 0.71 seconds with built imports: it reuses checked reverse and slice
lemmas rather than rechecking the reverse loop at each call. CBMC verified the
unchanged bounded harness at `N=8` in 5.18 seconds and timed out at `N=16` after
10 seconds. These compare proof checking with automatic bounded search; checking
time excludes writing the annotations. `make benchmark-scale` includes all five
new Lean contracts and all five bounded workloads.

## Nested loops and permutation: bubble sort

`Proofs/BubbleSort.lean` now proves the unchanged program for every representable
unsigned length, with readable 32-bit elements and a nonwrapping 56-bit pointer
extent. Its `verify` theorem establishes signed pairwise `Increasing` order,
a standard Lean `Array.Perm` of all original values, preservation of every byte
outside the array, safety and completion within `5*((n+1)*(n+2)+2)` original
interpreter blocks. Permutation preserves multiplicities, including duplicates.
Empty and singleton arrays are included. This is a conservative quadratic bound,
not an exact execution count.

The 310-line file keeps the mathematical and execution arguments together:

- The outer checkpoint tracks a sorted suffix, with every earlier element below
  every element in that suffix.
- The inner checkpoint also tracks the maximum of the scanned prefix.
- Each swap preserves the permutation and byte frame. The proof traverses the
  actual one-block swap callee and its return continuation in a five-block path.
- One natural-number rank combines progress of both loops. The existing proved
  path and rank rules turn these checkpoint obligations into bounded completion
  of the original generated program.

About the first 100 lines are contents, ordering, permutation and memory lemmas;
the rest is the checkpoint invariant, its block obligations and the final
contract. All helpers remain in this example. No shared proof module, tactic,
C++ printer or interpreter change was needed for sorting. `Audit.lean` reports
only standard Lean axioms; there are no unfinished proofs or native-decision
certificates. `make check` checks all seven entry contracts and all 3,150 concrete
case records.

The fresh sorting proof-file check took 1.17 seconds with built imports. CBMC
verified `N=4` in 1.37 seconds and timed out at `N=8` and `N=16` after 10 seconds.
The complete sorting proof, including its local mathematical lemmas, is checked
in that Lean file run. Shared dependencies are already built. These figures do
not include constructing the invariants or measure general verification effort.

## What still limits scaling

All seven entries in this suite now have universal correctness and termination
results under their explicit memory and ABI preconditions. The nested-loop
example is substantially more verbose than the 68–95-line scans. Loop invariants,
array mathematics, pointer normalization and ranking functions remain manual;
proof checking time does not measure that effort.

Rotation demonstrates callee-contract reuse within one shared generated bundle.
The sorting proof follows its tiny swap callee directly; it does not establish
transport of contracts between independently generated bundles. The entry view
is handwritten, and proofs still name generated PCs and local fields. More work
on a small proof-facing interface should be driven by another real caller or
algorithm rather than by adding a general framework preemptively.


## Reviewing the claims separately

`Spec.lean` is the review entry point for all seven functions. It states the
requirements and results directly, without loop invariants, generated PCs or
proof tactics. `Spec/Array.lean` contains the shared array and frame definitions,
relocated unchanged from `Proofs/Array.lean`. The implementation proofs and their
public theorem statements are unchanged.

`Verified.lean` proves each review statement from those implementation theorems;
its seven theorems are included in the axiom audit and checked by the default
build. The specification exposes universal safety, termination and behavior,
while the implementation theorems retain their explicit block bounds. The
separate review statements are checked against the proofs, rather than relying
on prose summaries staying in sync.
