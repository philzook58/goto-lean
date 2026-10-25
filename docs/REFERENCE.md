# Reference

A small C++ printer from CBMC GOTO binaries to readable Lean 4. Expressions use
native `BitVec` operations. Arbitrary control flow uses named basic blocks and
an explicit PC. Generated comments retain GOTO instruction numbers, source
locations, assertion property IDs, and CBMC location comments, including ASMC's
assembly/p-code descriptions.

The same generated block definitions support unbounded safety proofs with
`vcgen` and bounded concrete execution. The translator is not formally verified.
The compatibility target is the executable GOTO IR of the pinned CBMC version,
including parser and lifted-code workloads. [Coverage and the implementation
sequence](../COMPATIBILITY.md) track the remaining gaps; the current subset is an
implementation milestone, not the intended endpoint.

Commands below run from the repository root unless stated otherwise.
For a first session, use [the short tutorial](TUTORIAL.md).

## Build

Requires a C++17 compiler, CMake 3.24+, Bison, Flex, zlib development headers,
and Lean/Lake **4.35.0** (normally installed through elan). Tests also use Python 3
and a native C compiler. The printer has no Python or Lean runtime dependency.

```sh
cmake -S . -B build -G Ninja
cmake --build build --target goto-lean-tools -j4
lake build
ctest --test-dir build --output-on-failure
```

CMake fetches CBMC commit `32441ee38f8b2be63281a88a0df1a585dd4fdc43` (6.11.0).
CBMC also fetches MiniSat as a transitive build dependency. No preinstalled CBMC
is needed. Override `GOTO_LEAN_CBMC_REV` to change the pin, or use the standard
`-DFETCHCONTENT_SOURCE_DIR_CBMC=/path/to/cbmc` to reuse a source checkout.

The default build produces only `goto-lean` and its libraries. The explicit
`goto-lean-tools` target also builds `goto-cc`, `goto-instrument`, and the IR test fixture generator.
Set `-DBUILD_TESTING=OFF` to configure without Python/Lake discovery.

## Translate and execute

```sh
mkdir -p build/demo
build/bin/goto-cc -c examples/scalars.c -o build/demo/scalars.gb
build/bin/goto-lean build/demo/scalars.gb --function increment -o build/demo/Increment.lean
lake env lean -o build/demo/Increment.olean build/demo/Increment.lean
LEAN_PATH=build/demo lake env lean --run examples/Run.lean
```

`examples/Run.lean` uses both `#eval` and an ordinary `IO` entry point. Incrementing
41 returns 42; incrementing `0xffffffff` wraps to zero. The generated module
imports `GotoLean`, so build the shared library with `lake build` first.
`LEAN_PATH` makes the generated modules visible to handwritten harnesses.

Use `--object-bits N` on both `goto-lean` and the comparison `cbmc` command when
changing CBMC's default pointer split. The printer validates it against the input
pointer width, aligns CBMC's maximum-allocation constant, and records it in the
header. More object bits leave fewer offset bits. Receipt policies accept an
optional `"object_bits": N` (default 8); use the same value in separate comparisons.

Each generated namespace is `v_` followed by the sanitized GOTO function name:

```lean
v_increment.run (x : BitVec 32) : GotoLean.Program (BitVec 32)
v_increment.eval (x : BitVec 32) (fuel : Nat) (choices : List Nat := []) :
  GotoLean.Outcome (BitVec 32) × List Nat
```

The first component of `eval` is one of:

| Outcome | Meaning |
| --- | --- |
| `returned value` | Normal return |
| `assertionFailed site` | A GOTO assertion failed |
| `assumptionRejected site` | This path violates an assumption |
| `choiceError site` | Missing or out-of-range nondeterministic input |
| `exhausted block` | The basic-block budget ran out |

Fuel counts entered basic blocks, including the final return block. Only
`returned` is a completed execution. The second component contains unused
choices, permitting replay and detecting unexpected choice consumption.

Choices are unsigned `Nat` bit patterns in execution order and must fit their
requested widths. Every executed GOTO declaration consumes a choice, even when
an assignment immediately overwrites it. For `constrained`, `[0, 0, 9]` supplies
two declaration values followed by the nondeterministic call result. An
uninitialized scalar remains stable between writes. Boolean choices consume
one bit; C `_Bool` storage retains its CBMC bitvector width.

## Prove

The [agent proof guide](AGENT_GUIDE.md) maps these APIs to concrete replay,
universal completion, loop invariants and certified counterexamples.

`run` expresses safety on every finite execution prefix and a postcondition on
normal returns. It permits divergence. A failed check before divergence still
violates safety; `assume false` discards its path.

`GotoLean.run_spec` proves a function using an invariant on its `(PC, Locals)`
frame. Its preservation obligations are finite block specifications handled by
`vcgen`. The small effect language represents only choice, checks and assumptions;
there is no expression AST or general GOTO interpreter in Lean.

The printer preserves explicit blocks and declaration choices. Simplification
belongs in Lean proofs or handwritten summaries proved equivalent to the
generated definitions; the printer does not fold return blocks or eliminate
overwritten values.

The handwritten [proof examples](../examples/Proofs.lean) prove wrapping increment,
unsigned maximum, a countdown loop, and a constrained nondeterministic result.
CTest generates their imported modules under `build/tests`; after running it:

```sh
LEAN_PATH=build/tests lake env lean examples/Proofs.lean
```

The shared library proves `evalLoop_exec` (concrete results have a finite
operational execution witness) and `run_eval_sound` (unbounded specifications
apply to every concrete execution bound). Public claims listed in the example
audits use `#check_axioms` from
`GotoLean.Audit`: unexpected transitive axioms (including `sorryAx`) and unknown
names fail compilation. Only `propext`, `Quot.sound` and `Classical.choice` are
allowed. Passing checks are quiet; unaudited declarations are outside this gate.
`failure_refutes` turns a proved failing replay into an operational witness and
a refutation of the unbounded safety specification for any postcondition.

The optional [call-contract rule](../GotoLean/Contracts.lean) derives whole-program
safety from local function contracts and continuation obligations. It proves
recursive calls without requiring a user-written stack invariant. The
[factorial proof](../tests/Contracts.lean) establishes the generated function's
result modulo 2^32 and unchanged memory for every input, with partial correctness
rather than termination. [Memory lemmas](../GotoLean/MemoryLemmas.lean) give snapshot
copy contents, byte-level frame conditions and preservation of object extents.
These proof modules are separate from the executable definitions and the C++ printer.

[The self-contained parser example](../examples/parser/README.md) is the complete
proof workflow: `make generate`, `lake build`, then
`lake env lean --run Run.lean`. It verifies all three scanning loops and the
helper call for NUL-terminated inputs under explicit memory preconditions.
Its client proofs use `Memory.ValueAt`, `Memory.BytesAt`, and the parser's
`Parsed` contract. [Word and frame lemmas](../GotoLean/MemoryViews.lean) hide the
32/64-bit byte packing. Generated files name the pointer ABI, annotate PCs with
source positions, and wrap long effect expressions; paths are relative to the
translator's working directory.

Correctness claims can also live directly in C. The
[C assertion examples](../examples/checks/README.md) prove five source assertions
and six CBMC-inserted safety properties in Lean, using the same instrumented GOTO
input as CBMC. Read `examples/checks/checks.c` for the assumptions and assertions;
no separate functional Lean specification is needed for those examples. This
covers selected bounds, signed-overflow, division and shift-distance checks.
Pointer instrumentation also runs on the array suite; instrumented fill now has
an unbounded proof covering all six of its imported pointer assertions. Read
[its contract](../examples/arrays/Spec/CheckedFill.lean) for the exact memory
preconditions and [the safety report](../examples/arrays/SAFETY.md) for remaining gaps.

For reviewing array correctness claims without reading proofs, start with
[`examples/arrays/Spec.lean`](../examples/arrays/Spec.lean): it gives preconditions,
results and a plain-language explanation for each entry. The default example
build checks [`Verified.lean`](../examples/arrays/Verified.lean), which connects all
seven claims to the implementation proofs. Their C sources are under
`examples/arrays/upstream/`.

[The ACSL array examples](../examples/arrays/README.md) translate unchanged upstream
`lower_bound`, `reverse`, and `swap`. Their Lean contracts prove the partition
result, in-place reversal, and memory frame conditions. Both entry points also
have termination proofs using the optional [bounded-completion rules](../GotoLean/Termination.lean).
Search now annotates only entry and the loop header using the checked
[path combinator](../GotoLean/Paths.lean), with the original generated blocks unchanged.
Reversal reuses it across the original swap call, sharing one loop argument
for correctness and termination.
A one-comparison mutation has an operational counterexample certified by the Lean kernel.
Run `make check` in `examples/arrays`; `make cbmc` compares bounded verification separately.
[The scaling suite](../examples/arrays/SCALING.md) adds five entries and five more
universal contracts. Rotation reuses the reverse theorem across its three original
calls using a shared generated body and a proved Lean call-composition rule.
Bubble sort proves ordering, permutation, byte framing and termination across
its two nested loops using the existing Lean checkpoint rules.

## Current subset

Supported: Boolean and fixed-width signed/unsigned bitvectors, C enums,
constant-length arrays, structs, little-endian unions, parameters, automatic
locals, assignments, declarations/lifetime markers, branches, assertions,
assumptions, and value/void returns. Expressions include arithmetic,
bitwise/Boolean operations, comparisons, shifts, casts, conditionals, aggregate
constructors, string literals, array reads, and nested index/member updates.
Nondeterministic expressions and supported zero-argument external `nondet_*` /
`__VERIFIER_nondet_*` calls produce explicit choices.

Aggregate values use packed native `BitVec`s. Field widths and offsets come from
CBMC's own `boolbv_widtht`, including explicit padding. Small Lean helpers perform
field replacement, repeated-array construction and reads. For aggregates kept as
values, out-of-bounds reads choose an unconstrained value, while out-of-bounds
array updates leave the packed value unchanged, matching CBMC's finite-array
encoding. Supply CBMC-instrumented bounds assertions to prove array safety.

Address-taken automatic locals instead use shared object memory, implemented in
[Lean](../GotoLean/Memory.lean). Native bitvector pointers encode object identity and
byte offset, with scaled arithmetic and little-endian loads/stores. Direct
accesses and aliases share the same bytes, including updates through `char **`.
Memory functions accept an optional `memory` argument and return `(result,
memory)`; scalar/value-only functions retain their existing interface. Local
objects die at `DEAD` or function exit. Invalid loads/stores fail explicit safety
checks labeled `memory read` / `memory write`.

This slice covers automatic objects, heap allocation and caller-supplied pointer parameters.
It requires eight-bit bytes, matching packed/object layouts and one
pointer width; 32- and 64-bit ABIs are tested. Taking a parameter's address is
still unsupported. IDs are fresh and finite, so repeated allocation can exhaust
them. See [the compatibility notes](../COMPATIBILITY.md#first-object-memory-slice)
for the exact scope, extra safety checks and remaining provenance/layout work.

Direct calls include reachable callee bodies in the same generated module.
Each function keeps its own named locals and PCs. A small [Lean call stack](../GotoLean/Calls.lean)
handles nested calls, recursion and mutual recursion; C++ does not inline bodies.
Caller continuations receive the callee's updated memory before storing its
result. Fuel counts blocks across the whole call tree. Functions with ordinary
calls return `(result, memory)`; call-free scalar/value interfaces are unchanged.
For bounded modular proofs, import `GotoLean.CallSummary` and compose proved
callees with `finishes_resume`. `ReturnPost tag Q` lifts a predicate on a typed
payload (including memory) to the tagged return value; destructure its witness
at the continuation instead of splitting every return variant.

When external `memcpy` or `strlen` has no GOTO body, the printer emits a call to
the checked [Lean library model](../GotoLean/Library.lean). Copies check complete
source/destination ranges and non-overlap, preserve other bytes and return the
destination pointer. String length requires a NUL inside the object. These are
explicit library models with `vcgen` rules, not unconstrained external returns.
Supplied GOTO bodies take precedence over these models. For heap allocation, use
`goto-instrument --add-library` on a linked GOTO binary to preserve CBMC's
malloc/free/calloc bodies and failure policies; see [heap-model usage and limits](../COMPATIBILITY.md#loading-cbmcs-heap-model).

Division and remainder use native bitvector operations on nonzero divisors and
nondeterministic results on zero divisors, matching the pinned CBMC bit-blasting
encoding. Arithmetic translation does not add C undefined-behavior checks: supply
GOTO IR with those assertions already instrumented when proving C-level safety.
Supported signed/unsigned addition, subtraction and multiplication overflow
predicates print as native Lean `BitVec` overflow operations. Instrumentation
coverage remains selective; pointer checks now run on all seven array examples. See
[the C assertion examples](../examples/checks/README.md). Arithmetic and oversized
shifts otherwise follow fixed-width IR operations. Constant shift
distances outside CBMC's nonnegative signed-int range are rejected; dynamic
bitvector counts use their unsigned bit patterns. A proved left-shift helper
avoids constructing enormous intermediate natural numbers on oversized counts.

See [the compatibility inventory](../COMPATIBILITY.md) for supported features and
remaining gaps. Unsupported features are rejected when reachable; unrelated
functions are not translated. Errors identify the function, instruction and
available source location. Translation finishes before atomically replacing the
destination file.

This memory milestone does not yet translate ASMC's full pointer-based machine
state. Termination is established for seven array entries under their preconditions;
other function contracts may provide only partial correctness. No binary/source-to-Lean
correctness theorem is provided.

## Validation

CTest type-checks generated modules and completed `vcgen` proofs, compares concrete
Lean runs with compiled C over boundary/random inputs (including aggregates),
replays identical choices
through native assertion/assumption harnesses, and compares IR arithmetic edge
cases against CBMC's constant-expression oracle. Native C comparisons stay within
defined C arithmetic domains. It also tests irreducible control flow, declaration
havoc, lazy choices, bounds, escaped source comments, malformed inputs, and output
preservation. A corrupted expected result verifies that differential comparisons
detect disagreement.

[The memory runner](../tests/memory.py) separately checks aliasing, byte order,
pointer scaling/subtraction, lifetime and observable caller-memory effects.
[Lean proofs](../tests/Memory.lean) certify the concrete `char **` execution and
null/bounds/lifetime failures, using only standard axioms. Run it alone with
`python3 tests/memory.py`. The same source can be checked independently with CBMC:

```sh
cbmc tests/memory.c -D__CPROVER__ -DHARNESS --function main --bounds-check --pointer-check --no-signed-overflow-check
cbmc tests/memory.c -D__CPROVER__ --function null_bad --bounds-check --pointer-check --trace
cbmc tests/memory.c -D__CPROVER__ --function bounds_bad --bounds-check --pointer-check --trace
cbmc tests/memory.c -D__CPROVER__ --function dead_bad --bounds-check --pointer-check --trace
```

The first succeeds; the other three find memory-safety counterexamples (exit 10).
The explicit overflow flag limits this comparison to memory: CBMC 6.11.0's
default signed-overflow check flags the valid negative pointer difference in
`backwards`. Native C with UBSan and generated Lean both return `(unsigned)-3`;
the native harness passes with undefined-behavior and pointer-overflow sanitizers.
This CBMC discrepancy is separate from the three intentional memory failures.

[Call regressions](../tests/calls.py) cover recursion, mutual recursion, aggregate
and void returns, shared caller objects, 32-bit calls and library models.
[Proofs](../tests/Calls.lean) certify recursive execution, a failing callee and
library failures, and use `vcgen` to prove a memcpy frame property.

The [parser experiment](../experiments/parser/run.py) translates the unchanged
local repair helper `take_word` and its existing harness from the Cornell
serial-assurance experiment, without inlining or replacing the
helper. It compares native and Lean results, all 16 output bytes and cursor
positions on 195 inputs/capacities, including rejected and high-byte inputs.
[A kernel-checked execution](../experiments/parser/Proofs.lean) certifies a complete
copy-and-advance case. The same [universal parser proof](../examples/parser/Proofs/TakeWord.lean)
is checked against this unchanged external helper as well as the self-contained
example. It proves success and rejection, including the cursor and memory frame,
for any NUL-terminated input satisfying its documented 64-bit memory preconditions.
Run it with `python3 experiments/parser/run.py`; it requires the sibling local
experiment. See [source attribution](../examples/parser/SOURCE.md).
CTest also builds and runs the self-contained example; it does not depend
on that sibling.

[The paper coverage report](../experiments/paper/RESULTS.md) distinguishes the
original paper programs from the earlier scalar adaptations.

## Encoding experiments

[Small handwritten comparisons](../experiments/Encodings.lean) explore direct Actions,
typed block arguments, a collapsed loop, and native Lean `while`. They reuse the
existing runtime and are checked by CTest against the generated functions.
[Results and tradeoffs](../experiments/RESULTS.md) record source/proof sizes and the
limits of the comparison. The C++ printer and production semantics are unchanged.

[CBMC tutorial experiments](../experiments/tutorials/RESULTS.md) run examples from
the CBMC paper and Philip Zucker's tutorial through both tools. Lean discovers
three bitvector counterexamples, certifies failures in seven functions, and proves
the repaired lock loop safe for every 32-bit iteration count using a small
manual invariant. The array examples now also translate: the buffer overflow has
a checked failure certificate, and binary search has concrete replays. A short
reproduction script checks the examples and proofs;
a separate shell script times CBMC scaling against the Lean invariant proof.
Both are separate from the fast tests.

## Positive and negative controls

[The paired violation suite](../examples/violations/README.md) has 12 small C bugs
beside their repairs. Lean certifies failure of each named imported CBMC property
and a successful repaired execution; CBMC independently finds every violation and
checks each repair for all inputs. It covers source assertions, signed arithmetic,
division, shifts, indexing, null/dead/one-past pointers and loop bounds.
Both positive and negative Lean certificates run in CTest; paired CBMC runs are
also registered when CBMC is installed. New semantic/instrumentation coverage
should include both a successful return and failure of the intended property.
