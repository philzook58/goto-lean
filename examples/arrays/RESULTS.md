# Search/reversal experiment — 2026-10-21

Environment: CBMC/goto-cc 6.11.0, Lean 4.35.0, Linux x86-64.
Upstream revision and hashes are in `upstream/SOURCE.json`.

## Initial PC-invariant baseline

| Check | Outcome | Wall time |
|---|---|---:|
| CBMC, both contracts, symbolic length `n ≤ 8` | All 45 properties passed, including unwinding assertions | 1.67 s |
| CBMC, both contracts, symbolic length `n ≤ 32` | Timed out; no verification result | 30 s limit |
| CBMC, deliberate comparison mutation | Failed assertion; `[1,1,1]`, key `1`, result `3` | 0.06 s |
| Lean, array memory lemmas | Checked | 0.42 s |
| Lean, search correctness and termination | Checked for every representable length/key satisfying preconditions | 2.09 s |
| Lean, reversal correctness | Checked for every representable length satisfying preconditions | 1.03 s |
| Lean, reversal termination, including swap calls | Checked | 1.02 s |
| Lean, mutant execution and contract refutation | Kernel-checked witness | 0.53 s |
| Native C / Lean / independent Python | All 860 cases agreed for both algorithms | Not benchmarked |

The Lean entries are individual fresh `lake env lean Proofs/<file>.lean` file
checks with imports already built, not cached `lake build` timings. CBMC checks
bounds, pointers, signed overflow and complete loop unwinding. The combined C
harness checks both functions with symbolic arrays and a sorted-prefix assumption;
its failure to finish at 32 does not identify which algorithm dominates.
Results are single-run smoke measurements, not a controlled tool benchmark.

The Lean array, search and reversal proof checks total about 4.6 seconds after
imports are available. They require handwritten mathematical invariants, signed/
unsigned arithmetic bridges, memory frame lemmas, and termination arguments.
CBMC required a small C harness but no proof annotations. Thus this demonstrates
that annotations can replace expensive bounded exploration with a proof covering
all lengths; it does not establish lower total verification effort. No comparison
with Frama-C/WP was run here.

## Reproduce

```sh
make check
make cbmc
/usr/bin/time lake env lean Proofs/LowerBound.lean
/usr/bin/time lake env lean Proofs/Reverse.lean
/usr/bin/time lake env lean Proofs/ReverseTermination.lean
```

`cbmc.py` saves complete output to `.lake/cbmc-{8,32,bug}.txt`, reports a timeout
as inconclusive, and checks the expected exit code for every completed run. The
script also checks that the bug trace contains result `3`. `Audit.lean` prints the
axioms of both correctness proofs, both termination proofs, and the operational
counterexample certificates. Only the standard Lean axioms occur.

## What this says about the tool

The C++ printer needed no changes. The control-flow and function-contract rules
were sufficient for the original loops and the separate `swap` function. All new
reasoning lives in Lean. `GotoLean/Termination.lean` adds bounded completion and
a decreasing-rank rule in 58 lines, as an optional proof import.

The remaining usability cost is visible in the proof sources: the mathematical
invariants are small, but transporting them through PCs, local records, word
loads/stores and call continuations is still verbose. The search proof is much
shorter to use than to establish. Reversal termination currently unfolds one
four-block iteration explicitly. These examples are useful regression targets
for improving those interfaces, without adding transformations to the printer.

## Checkpoint experiment

The search proof was subsequently refactored to annotate only entry and the loop
header. `GotoLean.path` executes the original blocks until the next checkpoint or
return; exhausting its finite budget is a failed check. `finishes_paths` proves
that bounded completion of those paths implies bounded completion of the original
program. The proof uses `right-left` between visits to the loop header, with an
entry allowance, instead of assigning progress ranks to every intermediate PC.

| Source | Before | After |
|---|---:|---:|
| Search proof, including arithmetic helpers and public contracts | 142 lines | 115 lines |
| Shared path module | 0 | 54 lines |
| Combined | 142 lines | 169 lines |

Three small regression proofs are additionally kept in `tests/Paths.lean` and run
by `make check`. The original generated C/Lean and the array-memory helpers were
not changed. Both public search theorem signatures are checked unchanged. All
proofs use only standard Lean axioms.

A fresh pair of file checks with built imports took 1.01 seconds for the saved
old proof and 2.32 seconds for the new proof. These are single-run measurements;
the earlier timing table is the original baseline. Symbolically composing paths
currently costs more checking time. The improvement is fewer manual annotations
and a simpler progress measure, with a modest per-example line reduction. The
shared abstraction needs reuse before it saves total code; this experiment does
not justify building a larger automation framework.

## Reusing checkpoints for reversal — 2026-10-22

Reversal now proves correctness and termination together. Its one loop-header
invariant carries the array view and byte frame; induction on `half-i` decreases
between visits to that header. `path_finishes` handles the four original block
steps per iteration, including entering and returning from the separate `swap`
activation. Exit and entry use their actual two- and one-block costs, preserving
the existing exact `4*(n/2)+3` bound. Both public reversal theorem types are
unchanged. `ReverseTermination.lean` is retained as a one-line import for clients.

| Proof/helper source | Original | After reuse |
|---|---:|---:|
| Search | 142 | 115 |
| Reversal correctness and termination (including compatibility import) | 276 | 161 |
| Shared path module | 0 | 54 |
| Total | 418 | 330 |

The total includes the shared abstraction and is 88 lines smaller, about 21%.
The unchanged array-memory helpers and termination module are excluded on both
sides; the three small new path regression proofs are reported separately above.
No C++, generated code, array-memory helper, or shared path-module changes were
needed for this second use. No new automation framework was introduced.

A single fresh file-check pair, with built imports, took 0.67 seconds for a
combined copy of the old reversal and termination proofs and 0.63 seconds for the
new combined proof. This difference is too small to claim a performance gain.
The useful result is removing a duplicate loop argument while preserving its
contract and termination bound. The separate earlier search experiment remains
slower to check than its original PC proof.

`make check` checks the consolidated proofs and axiom dependencies, runs the three
path regressions, and compares all 860 concrete cases. The fixed small `swap`
callee can be traversed within a short path; this does not replace modular
function contracts for larger callees.

## Broader suite

[SCALING.md](SCALING.md) extends the experiment to five more entries and records
which have universal proofs, which only have bounded results, and where callee
composition and nested loops still need work.
