# CBMC compatibility

The target is the full executable GOTO IR emitted by the pinned CBMC version,
not a permanently scalar language. New versions and frontends can introduce
more types, expressions and instructions; unknown constructs must fail with
source information until their semantics are implemented. Merely serializing
an unknown node, inventing an axiom for it, or dropping its effects is not support.

The C++ printer remains a direct translation. Execution rules, memory operations
and proof rules belong in Lean. Any use of CBMC's own preprocessing passes must
be an explicit part of the input pipeline, with the resulting GOTO available
for inspection. No control-flow folding or choice elimination is hidden in the
printer.

## Current coverage

| Area | Status |
| --- | --- |
| Boolean, signed/unsigned bitvectors, enums | Implemented |
| Signed/unsigned addition, subtraction and multiplication overflow predicates | Native Lean `BitVec` operations; CBMC oracle tested |
| Fixed-size arrays, structs, nested member/index updates | Implemented as packed values |
| Union constructors, reads and updates | Little-endian values implemented |
| Aggregate parameters and returns | Implemented as packed values |
| Branches, irreducible loops, assertions, assumptions | Implemented for a single thread |
| Declarations, lifetime markers, scalar/value assignments | Implemented |
| Nondeterministic values | Implemented for supported finite value types |
| Effectful expression statements | Supported when the contained expression is supported |
| Address-taking, pointer arithmetic, dereferences, aliasing | Initial little-endian object memory implemented; see below |
| Globals/statics and initialization | Constant scalar value globals implemented; addresses and nonconstant initialization rejected |
| Direct calls, recursion, mutual recursion | Implemented with a Lean call stack |
| Indirect/variadic calls, unknown externals | Unimplemented |
| External malloc/free | Executable heap model, failure/success, arbitrary initial bytes, bounds and lifetime checks |
| Variable-length arrays, calloc/realloc, allocation intrinsics | Unimplemented |
| Byte extract/update, bitfields and remaining value operators | Incomplete |
| Floating/fixed-point, vectors and other specialized types | Incomplete |
| External memcpy / strlen | Checked Lean models when no GOTO body is supplied |
| Remaining library models and OTHER instructions | Mostly unimplemented |
| Threads, atomics, fences, blocking assumptions | Unimplemented |
| Exceptions and handlers | Unimplemented |
| Incomplete/unresolved GOTO instructions | Rejected; require a defined executable target |

Packed values use the pinned CBMC `boolbv_widtht` implementation rather than
duplicating layout rules in the printer. Only that small upstream implementation
is compiled into the printer; its SAT backend is not needed. The aggregate
helpers are ordinary Lean definitions, with no added axioms or expression AST.

## First object-memory slice

Address-taken automatic locals live in shared byte arrays. Their generated record
fields hold object addresses; direct reads/writes and indirect aliases use the
same Lean `Memory.load` / `Memory.store` operations. This includes a pointer
variable updated through `char **`. Objects retain the arbitrary bits chosen at
declaration until overwritten. `DEAD` and function exit invalidate local objects.
Pointer parameters take caller-supplied memory; returns expose the resulting
memory alongside the ordinary result so buffer/cursor effects can be checked.

Pointers retain native `BitVec` encodings: object bits above byte-offset bits.
The pointer width follows the input ABI (32 and 64 bits tested); object-bit width
currently uses CBMC's default configuration. Zero and one are reserved for null
and invalid objects. Offset arithmetic preserves object bits, scales by CBMC's
element byte size and wraps within the offset field. As in CBMC, ordered
comparisons between distinct objects return false and their pointer difference
is nondeterministic. A one-past address may be formed but not dereferenced.

This is a first executable memory model, not full CBMC memory compatibility:

- Memory requires little endian, eight-bit bytes and layouts where packed value
  bits agree with object bytes. Mixed-width pointers, non-byte fields and layout
  mismatches are rejected. Taking a parameter's address is not implemented yet.
- Each allocation uses a fresh object ID; released IDs are never reused. The
  finite ID space can be exhausted, including by repeated declarations in loops.
  It then fails explicitly. IDs follow this model's allocation order; a
  correspondence with CBMC's numbering, including pointer/integer casts, is not
  established. Allocation identity/reuse and provenance need further comparison
  before claiming unbounded loop/recursion compatibility.
- Loads/stores add explicit object-lifetime and whole-object bounds checks.
  Failure sites end in `memory read` or `memory write`; these checks are additions
  to raw GOTO, not imported source assertions. Their witnesses refute the Lean
  safety model. CBMC separately confirms the corresponding C memory errors.
  Subobject bounds, alignment, effective types and the other C safety obligations
  still require instrumentation and/or further memory-model work.
- Value-only globals with constant scalar initialization (including implicit C zero
  initialization), including local statics, are shared across calls. Global addresses, variable-length arrays and remaining library effects are still unsupported.
- Pointer object/offset/invalid predicates and live object sizes are implemented.
  Unknown/dead object sizes are unconstrained: discarded extents are not modeled.
  This introduces a universal nondeterministic choice for an unavailable extent;
  it is not a proof that the whole memory model conservatively represents CBMC.

`tests/memory.py` is a separate, purpose-specific runner. It checks native C
against generated Lean, plus a 32-bit cursor probe. `tests/Memory.lean` contains
kernel-checked execution/failure witnesses and observable parameter-memory
effects. `GotoLean/Memory.lean` supplies `vcgen` specifications for allocation,
loads and stores, byte read-after-write and disjointness lemmas. General
multi-byte load-after-store proofs remain to be added; multi-byte execution is
covered by differential tests.

## Direct calls and library effects

The entry's reachable direct-call graph is printed once, including recursive
cycles. Each function retains its own locals and explicit PCs. The shared Lean
`Transfer`/`callStep` runtime pushes caller continuations and pops them on return.
Tagged results support all implemented return types; continuations restore caller
locals but take the updated callee memory. Local objects die on callee exit.
The existing `run`, `Executes` and fuel-bound evaluator apply to this ordinary
combined step function. Fuel is shared across caller and callee blocks.

Call results currently require a local-symbol destination, including an
address-taken local. Complex lvalues, indirect calls and variadic calls fail
explicitly; arguments must carry explicit GOTO casts matching the callee's
parameter types. General function pointers and address-taken parameters remain
future work. No inlining, loop structuring or declaration-choice elimination
is hidden in the printer.

Four external library names have explicit Lean semantics when no GOTO body is
available. A supplied body always takes precedence:

- `memcpy` checks whole source/destination ranges and non-overlap, copies the
  original bytes, preserves other bytes and returns the destination pointer.
  Null/dead pointers fail even for zero length. It is an atomic library model:
  fuel does not count individual copied bytes.
- `strlen` checks the pointer and requires a terminator within the same object;
  it returns the number of preceding bytes. It has no memory effects.
- `malloc` chooses failure or success and, on success, arbitrary bytes. A fresh ID
  and the requested extent are stored in ordinary memory; heap ownership is separate
  from automatic-object ownership. Zero-sized allocations may return null or a
  fresh empty object.
- `free(NULL)` changes nothing. Other frees require a live heap base: stack pointers,
  interior pointers and double frees fail explicitly. Release invalidates the object
  and records `__CPROVER_deallocated` for imported pointer checks.

These use the current object-memory validity rules, including their documented
limits. Heap failure is always possible, matching CBMC comparisons with
`--malloc-may-fail`. IDs are finite and never reused; success beyond ID/extent
capacity fails a model check. This does not establish arbitrary allocation-loop
compatibility. Loaded malloc/free bodies retain precedence and may contain
unsupported allocation intrinsics. `calloc`, `realloc`, leak detection, allocation
failure modes/limits and new/delete bookkeeping are outside this slice. These
explicit C library models do not establish equivalence to every CBMC built-in
library implementation. `tests/Calls.lean` includes kernel-checked
recursive execution and callee/library failures, plus a general `vcgen` memcpy
frame proof. General modular function-contract rules and universal parser
invariants remain proof-interface work.

## Small positive and negative controls

These extend the existing runners; generated Lean stays under `build/`.

| C pair | Lean evidence | Independent comparison |
| --- | --- | --- |
| `offset_good` / `offset_bad` in `tests/memory.c` | Interior-pointer subtraction returns 11; moving before the array has a certified failed memory check | Native C on defined inputs; CBMC passes the good function and finds `offset_bad.pointer_dereference.2` |
| `separate_good` / `separate_bad` in `tests/memory.c` | A store preserves the other object's value 7; the false assertion on input 9 has a certified failure | Native C on the good function; CBMC proves it and finds `separate_bad.assertion.1` |
| `heap_roundtrip` / `heap_dead` in `tests/memory.c` | Successful allocation/store/load/free and allocation-failure executions; certified use-after-free failure | CBMC proves the guarded caller and finds the lifetime error |

The memory runner adds 180 native comparisons and four concrete Lean certificates
with axiom audits. These certificates establish particular executions, not universal
safety. Negative memory accesses are never executed natively. CBMC comparisons above
were run separately with `--pointer-check --bounds-check`; their JSON is local build data.
`tests/Heap.lean` adds a universal allocating caller: every input is returned and
no allocation remains live, covering failure and arbitrary initial bytes. Other
certificates cover use-after-free, double/interior/stack free, bounds violations
and unchecked allocation failure. Nonzero initial bytes and successful zero-size
allocation/free are regression controls. The memory runner also replays an
instrumented heap caller and, when CBMC is installed, checks all nine heap entries
with allocation failure enabled. Parameter-address rejection remains tested.

Run `python3 tests/memory.py build` for the memory and heap tests. CBMC comparison
JSON stays under `build/memory/`; failing examples must exit with code 10.

## Parser-driven order

1. **Finite aggregate values.** Implemented first because the existing parser
   harness starts with byte buffers. Check nested updates, padding, enum signs,
   constructors and functional updates against native C and CBMC's expression
   simplifier. Bounds assertions remain explicit GOTO assertions.
2. **Object memory and globals.** Model object identity, offsets, extents,
   initialization, byte order, validity and lifetime together. Address-taken
   locals and direct variable accesses must see the same storage. Aliases must
   not become separate Lean values. In particular, a store through `char **`
   must update the caller's cursor.
3. **Calls and library operations.** Direct calls/recursion and checked
   `memcpy`/`strlen` models are implemented. Extend to function pointers,
   remaining externals and modular function contracts. Explicit CBMC inlining
   remains an optional input preprocessing step.
4. **Remaining sequential types and operators.** Include IEEE floating-point
   conversions, rounding, NaNs and infinities, byte-level operations, dynamic
   objects and instrumentation predicates. The parser's numeric branches need
   these semantics; declaring those branches unreachable would narrow the claim.
5. **Remaining execution mechanisms.** Exceptions, threads, scheduler choices,
   atomic regions, fences and memory-model instrumentation need explicit
   semantics. The current single-thread interpretation of `assume` cannot
   simply stand in for a thread waiting on a mutable condition.

Each step needs real GOTO fixtures, concrete comparisons where C behavior is
defined, failing examples with checked witnesses, and reusable Lean semantics.
Keep the ordinary scalar/aggregate regressions independent of a sibling project.

## The actual blocking input

The Cornell project already contains the parser; a new scalar recognizer would
not verify it. Reproduce translation from this project directory:

```sh
mkdir -p build/parser
build/bin/goto-cc -c ../cornell-serial-assurance/harness/check_word.c -o build/parser/word.gb
build/bin/goto-lean build/parser/word.gb --function main -o build/parser/Main.lean
build/bin/goto-lean build/parser/word.gb --function take_word -o build/parser/TakeWord.lean
```

Both translations now succeed. `take_word` calls its unchanged `copy_word`
helper, including its `memcpy` effect. The existing harness also translates its
`strlen` calls and source assertions. No inlining is required.

The experiment uses the actual helper from
`cornell-serial-assurance/generated/take_word.inc`:

```sh
python3 experiments/parser/run.py
```

It compares result flags, cursor positions, every output byte and unchanged
input bytes with native C on 195 cases. A kernel-checked execution certifies
copying `hi`, its NUL terminator and cursor advancement while preserving other
bytes. A concrete execution of the original harness reaches and passes its
successful `strlen` and pointer-range assertions.

The unchanged helper/harness can now be translated and executed. A universal
correctness proof remains to be written. The full command parser still needs
addressable global storage, more string/numeric library operations and floating point.
**This is not full parser verification.**


## Imported safety properties and C assertions

`examples/checks/checks.c` makes preconditions and functional guarantees visible
as CPROVER assumptions and assertions. Five Lean completion proofs check those
source assertions and six properties inserted by `goto-instrument`, retaining
source/property IDs. The same instrumented GOTO binary is given to CBMC, with
analysis-time default checks disabled. It covers array indexing, signed
negation/addition/division overflow, division by zero and unsigned shift distance.
The new overflow mappings add 144 signed/unsigned CBMC oracle comparisons across
widths 8, 32, 64 and 128 to the regular regression suite.

This is selective instrumentation coverage, not a claim that all CBMC checks
translate. Pointer instrumentation now translates and runs on all seven array
algorithms, including mutable CPROVER state. `--bounds-check` alone inserts no
bounds property for those pointer-based bodies. Their C assertion harnesses pass
CBMC with all values and lengths up to four; the instrumented Lean code passes
3,150 concrete comparisons and seven kernel-checked execution certificates.
Instrumented fill now also has universal safety, contents, framing and termination
proofs, under explicit readable-array, nonwrapping and object-state preconditions.
The other six universal array proofs still concern raw GOTO and do not establish
the added properties universally. See
[`examples/arrays/SAFETY.md`](examples/arrays/SAFETY.md) for the exact policy,
commands, results and limitations.

## Assurance limits and improvement plan

[CONFIDENCE.md](docs/CONFIDENCE.md) covers specification adequacy, assumption
vacuity, theorem scope, instrumentation, artifact identity, translation/model
fidelity, axiom policy and deployment, together with current safeguards and next steps. Compatibility tests and
unbounded proofs of the emitted model do not themselves prove C/CBMC equivalence.
