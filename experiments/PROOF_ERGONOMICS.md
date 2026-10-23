# Proof ergonomics audit

Simple call-free scalar proofs are quite tractable. The current example proofs
make increment and maximum look harder than necessary by introducing invariants
even though both functions always return after two blocks. Their expressions
are ordinary Lean bitvector arithmetic; the friction is mostly the dispatcher
interface, not the mathematics.

`ProofErgonomics.lean` checks summaries for every postcondition:

```lean
(v_increment.run x).wp Q ↔ Q (x + 1)
(v_maximum.run x y).wp Q ↔ Q (if x.ult y then y else x)
```

The summary proofs occupy about 10–13 tactic lines each. They account for all
fuel bounds, not just one successful bounded execution. Once proved, clients
need no PCs, local records or optional return values:

```lean
theorem increment_correct (x : BitVec 32) :
    (v_increment.run x).wp (fun r => r = x + 1) := by
  rw [increment_wp]

theorem maximum_correct (x y : BitVec 32) :
    (v_maximum.run x y).wp (fun r => r.toNat = max x.toNat y.toNat) := by
  rw [maximum_wp]
  split <;> simp_all [BitVec.ult, Nat.max_def] <;> omega
```

These are proofs about the original generated definitions. The summary setup
cost is real, and is amortized when proving more than one property. It does not
eliminate the C++ translation trust boundary. Bitvector increment wraps; this
statement does not assert unbounded natural-number addition without overflow.

## Current readability

The initial audit's generated files contained 47 lines for increment, 48 for maximum,
60 for countdown, 221 for the nested-call fixture and 235 for take_word including
its copy helper. Counts include imports, types, blank lines, source comments and
execution wrappers; they are observations, not a benchmark or a stable format.

The arithmetic and source references are readable. Most visual noise comes
from PC names such as `b27`, repetitive record updates, the optional return slot,
long source-site strings, explicit pointer-layout numbers and call-stack
dispatch. Memory and call programs need considerably more scaffolding than a
handwritten Lean program expressing the same intent.

Loops remain manageable on the scalar fixtures: the existing countdown and
repaired-lock proofs use small PC-indexed invariants and vcgen. Those proofs
establish safety and partial correctness, not termination. For calls and memory,
concrete replay is easy. The later universal factorial and parser proofs now
exercise modular contracts and the memory proof interface; those are stronger
results than the original concrete execution certificates.

## Improvements worth making

1. Add a small Lean proof layer: summary lemmas for acyclic functions and a
   convenience invariant rule accepting block Hoare triples directly. Automate
   repetitive unfolding behind checked lemmas; keep the emitted program faithful.
2. Use `Memory.ValueAt` and `Memory.BytesAt` in `GotoLean/MemoryViews.lean`.
   The module now proves 32/64-bit load/store round trips and store frame laws;
   `MemoryLemmas` supplies slice-copy and object-extent laws. Parser annotations
   use these views for the input slice and stored cursor.
3. Use the new modular call-contract rule in `GotoLean/Contracts.lean`. It proves
   recursive factorial in `tests/Contracts.lean` without a user-written stack
   invariant. `examples/parser/Proofs/CopyWord.lean` supplies the actual helper's
   byte-level contract. `Proofs/TakeWord.lean` now proves all three scanning loops,
   rejection without memory changes, and successful output/cursor/input/frame
   properties. `Proofs/Scan.lean` derives the boundaries from NUL termination;
   the user does not supply them as assumptions. The proof's `Ready` predicate
   documents its 64-bit ABI, separate-object and no-wrap preconditions.
4. Presentation now includes relative source positions on PC declarations,
   named ABI constants, multiline function binders and wrapped effect expressions.
   The C++ changes format the same blocks, choices and memory operations.
5. The self-contained `examples/parser` project supports `make generate`, ordinary
   `lake build`, and `lake env lean --run Run.lean`. It is checked by CTest and
   needs neither a sibling project nor a hand-configured `LEAN_PATH`.

The setup proof is still substantial: the parser annotations remain tied to
generated PCs and explicit byte-memory semantics. The public client in `Run.lean`
uses the proved successful-return contract in a few lines, without PC, stack or
fuel reasoning. This is useful amortization, not automatic verification. The
complete command parser, termination and source-translation correctness remain
outside this proof.

A second CFG language or general structuring/optimization pass is not justified
by these examples. A checked summary already provides the small proof-facing
view, with the raw program still available for execution and auditing.

Recheck after the usual tests generate their modules:

```sh
LEAN_PATH=build/tests lake env lean experiments/ProofErgonomics.lean
```

The proofs use only standard axioms and have no sorries or native-checker axioms.
The scalar summary experiment does not change execution. The later printer
changes affect presentation; executable semantics remain unchanged.

## ACSL array case study

The [array examples](../examples/arrays/README.md) now prove unchanged upstream
`lower_bound` and `reverse`, including their original `swap` callee. Both also
have bounded-completion proofs, closing the termination gap for these entry points.
The C++ printer needed no changes. A one-comparison mutation has a kernel-checked
execution and a refutation of the original partition contract.

The reusable addition is an optional 58-line termination module; typed-array and
frame helpers stay local to the examples. Proof plumbing remains substantial:
about 530 lines for the array view, search, reversal and reversal termination.
The next ergonomics improvement should remove repeated state/arithmetic bridges
and make counted-loop proofs shorter, measured against these unchanged examples.
Do not mistake fast checking of a supplied proof for cheap proof construction.
[Measured results](../examples/arrays/RESULTS.md) record both the bounded CBMC
runs and fresh Lean file checks.

### Checkpoints on the search example

The search proof now has annotations only at entry and the loop header. A
54-line optional [path rule](../GotoLean/Paths.lean) checks finite paths through
the original blocks and connects their proofs to the original interpreter.
Exhausting the path budget is a failed check, so omitted loops cannot be ignored.
The same checkpoint proof establishes correctness and termination.

The search file shrank from 142 to 115 lines; with the helper included, total
code grew from 142 to 169 lines on this first use. A fresh old/new file-check pair
was 1.01/2.32 seconds. This is a small annotation/readability improvement, with
extra abstraction and checking cost. It should earn further use through another
concrete example before growing into a tactic or CFG reconstruction framework.

### Reuse on reversal

Reversal now uses the same path rule over its original call-stack interpreter,
including the separate one-block `swap` callee. One array/frame invariant and an
induction on `half-i` establish both the functional contract and the original
exact termination bound. The formerly separate 88-line termination argument is
gone; its module is a one-line compatibility import.

Search and reversal together fell from 418 to 330 lines including the 54-line
shared path module. This is an 88-line net reduction (about 21%), without more
shared helper code, new tactics, C++ changes, or modified public theorem types.
The experiment supports this small abstraction. It does not make the remaining
pointer arithmetic and array-frame proofs disappear, and large callees still
need modular function contracts.

### More examples, and the next scaling boundary

The [scaling suite](../examples/arrays/SCALING.md) adds universal contracts for
fill, first-match search and maximal sorted-prefix scanning in 88, 68 and 95
lines. Existing path and memory rules suffice; only two shared unsigned-index
lemmas (16 lines) were added. All seven translated entries pass native/Lean
execution comparisons, with rotation and bubble sort separately bounded-checked.
At that stage, their universal contracts had not been established.

That experiment exposed a concrete modularity gap: embedded reverse activations
had different generated types from the standalone reverse program targeted by
its theorem. The following experiment addresses this through a shared bundle.
Bubble sort then tests nested invariants and permutation reasoning. Timing and
coverage distinctions are recorded in the scaling report; short scans alone do
not settle those questions.

### Modular calls: reuse one reverse theorem three times

Rotation now has a universal total-correctness contract. The generated rotation
bundle already defines reverse and swap; a Lean entry view points the existing
reverse proof at that shared body. The new 46-line `GotoLean/CallSummary.lean`
proves that a completed callee contract can resume its caller, including nested
calls and checked returns. The 138-line rotation proof reuses `Reverse.verify`
three times and proves the three-reversal identity; it never unfolds the reverse
loop. Local slice/frame helpers take 102 lines, and the entry view takes 34.
The existing reverse proof gains eight lines to expose its completion contract.

This resolves the observed reuse problem within a shared bundle without C++
changes or a general state-transport framework. It does not transport the theorem
between independently generated bundles. `Generated.Reverse` remains an import
path for the entry view. The detailed contract, measurements and explicit costs are recorded in the
scaling report.


### Nested loops without a new proof framework

`Proofs/BubbleSort.lean` completes the seventh universal array-entry contract in
310 lines. It proves signed pairwise ordering, standard `Array.Perm` preservation
of all values including duplicates, byte framing, safety and a conservative
quadratic completion bound. It uses the existing five-block path combinator,
including the real swap call, with outer and inner loop checkpoints. A sorted
suffix and prefix maximum capture the mathematical progress; one natural-number
rank combines both loop counters.

All mathematical and memory helpers stay in the example file. No C++ code,
interpreter, shared proof rules, dependency or custom tactic was added. The proof
is longer than the simple scans, and still manually names generated PCs and
fields. This demonstrates that the existing semantics can handle nested-loop
sorting; it does not demonstrate automatic invariant discovery or annotation
cost independent of algorithm complexity. The scaling report separates fresh
proof checking from bounded CBMC search and records the remaining interface
limitations.
