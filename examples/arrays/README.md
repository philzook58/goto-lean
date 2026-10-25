# ACSL by Example: executable arrays and proofs

Seven upstream entries translate without algorithm changes or asking CBMC to inline
callees. Lean proves universal contracts for search, reversal, fill, first-match
search, sorted-prefix scanning, rotation and bubble sort. Every entry now has
a universal correctness and termination proof under its memory preconditions.
No changes to the C++ printer were needed.

[`caller.c`](caller.c) creates four local ints and calls instrumented fill.
Its [contract](Spec/Caller.lean) requires no input preconditions: every 32-bit
value is returned, the endpoint assertion passes, and the local storage is released.
The [proof](Proofs/Caller.lean) establishes fill's memory premises from allocation
and reuses the general fill theorem. Its buggy counterpart fills only three ints;
Lean certifies the named assertion failure on input 1. This caller has a fixed
capacity of four; the separate fill theorem handles arbitrary admitted lengths.

The allocation block is checked with an abstract continuation before composing
the call. This avoids unfolding the whole execution during type comparison.
A targeted check with `lean -j1 -M1024` passed in 2.53 seconds at 929,764 KiB peak
RSS (imports alone: 752,948 KiB). Both public claims pass the axiom audit.

## Review without reading proofs

Start with [`Spec.lean`](Spec.lean), alongside the corresponding
[`upstream/`](upstream) C function and header. Each entry has a plain-language
comment followed by the actual Lean proposition: inputs, preconditions and exact
result. The file's opening glossary explains its small shared vocabulary;
[`Spec/Array.lean`](Spec/Array.lean) contains the underlying definitions without
proof scripts. `TerminatesWith` includes safety, termination and the result,
while keeping implementation block counts out of the review statement.

[`Verified.lean`](Verified.lean) supplies one theorem per statement, for example
`Verified.bubble_sort : Spec.bubble_sort`. These are proved from the existing
implementation proofs, not assumed contracts. The default `lake build` checks
all seven links, and `make check` also audits their axioms and runs the execution
comparisons. The detailed invariants and tactics stay under `Proofs/`.

Your review question is whether the assumptions describe your intended inputs
and the postcondition says everything you need. For sorting, ordering alone
would allow an implementation that fills the array with zeroes: the explicit
permutation clause rules that out, including loss of duplicate values. The byte
frame requires the final bytes outside the array to equal their original values;
it does not specify intermediate write events. The statement quantifies over all
32-bit lengths satisfying its memory preconditions, rather than the concrete
lengths used by the test scripts.

The C tells you which implementation is under discussion. Lean checks the
connection between the generated interpreter and the written specification; it
does not decide whether that specification matches your intent. Translation
from C through CBMC and memory-model fidelity remain separate trust boundaries.
These seven claims are examples, not a claim of support for all CBMC IR.

For C-source specifications, see the separate
[`examples/checks`](../checks/README.md) demonstration: its source assertions and
selected CBMC-inserted safety checks are proved over the instrumented program.
The seven contracts in `Spec.lean` target raw algorithm translations. The separate
[`Spec/CheckedFill.lean`](Spec/CheckedFill.lean) now gives instrumented fill an
unbounded proof of all its imported checks as well. The matching C harnesses (`cbmc.c` and `scale_cbmc.c`) are bounded CBMC checks, not yet
universally proved assertion harnesses in Lean. The Lean memory-model checks
also do not amount to full CBMC pointer-instrumentation coverage.

## Run

With the main project's C++ tools built, run here:

```sh
make check   # regenerate, check proofs/axioms, compare native C and Lean executions
make cbmc    # original bounded symbolic checks, with a 30-second limit per check
make benchmark-scale # five more entries at three bounds, plus fresh Lean file checks
```

`check` needs make, Python 3, a C compiler, the project's Lean toolchain and the
two built GOTO tools. `cbmc` additionally needs CBMC on PATH. No example downloads
are needed. Source snapshots are checked against their recorded SHA-256 hashes.
The native compiler and goto-cc use C11 because the upstream headers typedef `bool`.

## Proved contracts

- [`LowerBound.correct`](Proofs/LowerBound.lean): for a readable, sorted array and
  any signed 32-bit key, the result lies in `0..n`, every element before it is less
  than the key, and every element from it onward is at least the key. The entire
  memory is unchanged. Duplicate keys return the first matching position.
- [`Reverse.correct`](Proofs/Reverse.lean): each final element equals the original
  element at `n-1-i`. Every byte outside the array is unchanged, including adjacent
  data in the same allocation. The proof follows the original
  generated `swap` call through the call-stack interpreter.
- `LowerBound.terminates` and [`Reverse.terminates`](Proofs/Reverse.lean):
  bounded completion of the original generated block interpreters, for all inputs
  satisfying the corresponding memory preconditions. Conservative block bounds
  are `8*(n+1)+6` and `4*(n/2)+3`. The search bound is deliberately loose.

- [`Fill.verify`](Proofs/Fill.lean) proves constant contents, the surrounding byte
  frame and termination. [`Find.verify`](Proofs/Find.lean) proves the first matching
  position or `n`, unchanged memory and termination.
- [`IsSortedUntil.verify`](Proofs/IsSortedUntil.lean) proves a maximal sorted prefix,
  unchanged memory and termination, including empty arrays and signed extrema.
- [`Rotate.verify`](Proofs/Rotate.lean) proves rotated contents, return value `n-k`,
  preservation of bytes outside the array and completion within `12*n+15` blocks.
  It reuses `Reverse.verify` three times across the original generated calls.
- [`BubbleSort.verify`](Proofs/BubbleSort.lean) proves signed pairwise ordering,
  a permutation of all original elements, the byte frame and termination within
  `5*((n+1)*(n+2)+2)` original blocks. Both loop invariants and the original
  `swap` call are checked; duplicate values are preserved.

`Values` is a mathematical function from indices to native `BitVec 32` values.
[`WordsAt`](Spec/Array.lean) connects each element to the existing little-endian
byte memory through `Memory.ValueAt`. Contracts compare signed `toInt` values;
indices use unsigned `toNat` arithmetic. Reversal, rotation, sorting and fill also require the
array's byte extent not to wrap the 56-bit pointer-offset field. Rotation
additionally assumes `k ≤ n`. The layout is the generated
64-bit ABI, not an ABI-polymorphic C theorem.

ACSL comments are preserved as specification references. They are not parsed or
trusted as Lean assumptions: their contracts and invariants were manually
expressed and proved in Lean. The `/*@ ... */` comments themselves are not
machine-checked by this workflow; they are upstream Frama-C annotations.
For a clause-by-clause reading of checked fill, see [the tutorial](../../docs/TUTORIAL.md#3-an-unbounded-loop-with-a-readable-contract).
Translation from C through CBMC and the fidelity of
the memory model remain trust boundaries. `Audit.lean` rejects theorem dependencies outside `propext`, `Classical.choice`
and `Quot.sound` with `#check_axioms`. There are
no unfinished proofs, custom axioms, or native-decision certificates.

## Concrete runs and a counterexample

[`Cases/Inputs.lean`](Cases/Inputs.lean) lists twenty named array cases and twenty
sorted search cases. It separately proves their memory, nonwrapping, machine-size,
lifetime-metadata, sortedness and pivot premises. [`Cases.lean`](Cases.lean) certifies
twenty normal returns for each of the seven instrumented algorithms (140 executions).
The existing native C/Lean/Python runners consume these same rows. Checks are split
by case to stay within a 1 GiB Lean limit. This tests useful admitted inputs; it
does not establish input or branch coverage.

`compare.py` supplies 860 cases to native C and generated Lean and checks both
against Python's independent `bisect_left` and sequence reversal. Cases include
empty arrays, duplicates, odd/even lengths through 256, signed extrema and keys
outside the array range. Lean execution also checks prefix/suffix sentinel bytes
around an array starting at a nonzero offset. These executions are tests; the
universal proofs are separate.

`prepare.py` creates a deliberate `<` to `<=` mutation in `.lake/`, leaving the
upstream snapshot untouched. On `[1,1,1]` with key `1`, it returns `3` rather than
`0`. CBMC finds the failed assertion in `bug.c`.
[`Counterexample`](Proofs/Counterexample.lean) uses kernel reduction to certify
that same generated execution, derives an operational execution witness, and
proves that the mutant violates the original partition contract. Lean checked a
supplied witness here; it did not discover the witness automatically.

## Size and comparison

The generated search is 131 lines. Reverse and swap now share the 295-line
rotation bundle, including source comments, locals, PCs, and execution entry
points. `Entries/Reverse.lean` provides its reverse entry; `Generated/Reverse.lean`
re-exports it instead of duplicating the body. The shared array view is separated
into `Spec/Array.lean` definitions and `Proofs/Array.lean` lemmas. The algorithm
proofs contain 115 lines for search and 168 for reversal including
termination. The old `ReverseTermination.lean` import path is retained as a
one-line re-export. The counterexample adds 37 lines. The shared
proof additions are a 58-line termination module and a 54-line path module.
Array helpers stay local until another example needs them; there is no ACSL
importer or new tactic framework.

Both algorithms now use the checked `path` combinator to traverse original blocks
between checkpoints. Search annotates entry and the loop header. Reversal has one
loop-header invariant, inducts over `half-i`, and traverses the actual call-stack
push/pop for `swap` within a four-block path. An exceeded path budget fails the
proof. Each algorithm derives correctness and termination from the same argument;
all four public theorem statements and both termination bounds are unchanged.

Before the modular-call experiment, search and reversal proof code fell from
418 lines to 330 including the 54-line shared path module and the compatibility
re-export. This was a net
reduction of 88 lines, about 21%. Reversal still explicitly supplies its array
view and frame lemmas; this is not automatic invariant discovery. Rotation now
demonstrates modular contracts across larger callees, as described in
[SCALING.md](SCALING.md).
Three regressions in `tests/Paths.lean` check that checkpoints cannot hide a failed
check, an omitted checkpoint, or a nonterminating cycle.

See [RESULTS.md](RESULTS.md) for measured checking times and bounded CBMC results.
The useful gain is proving all lengths once the annotations are available;
this experiment does not measure annotation effort or establish a general speedup.

## More examples and scaling

[SCALING.md](SCALING.md) records five more examples, five new universal contracts,
2,290 additional C/Lean/Python cases and per-entry bounded CBMC measurements.
It distinguishes proved contracts from bounded checks and records the shared
call-composition rule, array-slice helpers and the 310-line nested-loop sorting
proof. It also records the remaining manual annotation and generated-name coupling.
The generic checkpoint module and C++ printer did not grow. Proof reasoning stays
in Lean; rotation uses one generated body shared with its callees.

## Upstream

The C, headers and required ACSL logic files in `upstream/` are unchanged copies
from [ACSL by Example](https://github.com/fraunhoferfokus/acsl-by-example), revision
`3e8cd9adf79955d9b722185f9beb4518c66d57f2`. `SOURCE.json` records hashes;
`LICENSE.md` preserves the MIT license. `algorithms.c` only includes upstream C
files. The originals are under `StandardAlgorithms/BinarySearch`, `Mutating`,
`Nonmutating`, `Sorting`, `Logic`, and `StandardAlgorithms/typedefs.h`.

## CBMC safety instrumentation

`make checked checked-cbmc` translates and runs the seven algorithms with explicit
CBMC safety instrumentation and checks their bounded C assertion harnesses.
[SAFETY.md](SAFETY.md) records the exact check policy, successful results, Lean
execution certificates, and the remaining gap to universal instrumented proofs.
Instrumented `fill` now has its own unbounded safety, contents, framing and
termination proof. Read [its contract](Spec/CheckedFill.lean) and
[the proof-repair experiment](FILL_EDITS.md); the other six instrumented
algorithms remain to be proved universally.
