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

## ESBMC: feasibility probe, not a supported frontend

Tested the installed ESBMC 8.4.0 against our pinned CBMC 6.11.0. ESBMC's
[8.4 release](https://github.com/esbmc/esbmc/releases/tag/v8.4) adds a reader
for CBMC binaries; that is the opposite direction from importing ESBMC output.
Its [writer](https://github.com/esbmc/esbmc/blob/v8.4/src/goto-programs/write_goto_binary.cpp)
emits `GBF` with format version 1; CBMC expects `0x7f GBF` with version 6.
These are separate serializers, not a header that can safely be patched.

The probe used `int mymax(int x, int y) { return x > y ? x : y; }` and a
`main` asserting `mymax(42,43) == 43`:

| Route | Observed result |
| --- | --- |
| ESBMC `--output-goto` → goto-lean | Rejected: `not a goto binary`. |
| ESBMC `--goto2c --no-library --skip-bmc` → goto-cc → goto-lean | Scalar C maximum translated; Lean checked its result for all signed 32-bit inputs. |
| Python maximum → ESBMC `--goto2c --skip-bmc --python python3` → goto-cc | Export included about 10,700 lines of runtime code and failed C parsing (`} int;`). Disabling the library crashed this installed exporter. |
| CBMC binary → ESBMC `--binary` | Reader accepted the file, but verification aborted with `main symbol not found`, including with `--function main`. |

For the successful C export only, the manual adapter removed the version banner
and supplied `esbmc_intrinsics.h` containing
`#define assert(c) __CPROVER_assert((c), #c)`. It disabled ESBMC's library; it did
not replace library behavior with empty stubs. The Lean proof establishes the
exported maximum's behavior, not equivalence to ESBMC or Python. ESBMC returned
exit code 6 on some successful export-only commands, so file creation alone
must not be used as a general success test. Probe artifacts are disposable under
`build/esbmc-probe/`; there is no ESBMC dependency in the build or CI.

An ESBMC backend is possible, but it needs an explicit, version-pinned adapter
for instructions, types, expressions and runtime operations. Reuse the Lean
execution/proof library, reject unknown semantics, and compare positive and
negative executions before expanding the supported subset. The C-export route
is useful for experiments; these results do not justify a general-purpose
bridge or a claim of additional language support yet.

## Current coverage

The [Frama-C collection examples](examples/case-studies/README.md) exercise jsmn,
2048 row moves, and khash lookup against native C. They include real and deliberate
violations. Full pointer-instrumented jsmn now compiles and executes under the
current Lean memory budget; its kernel counterexample replay still uses a lighter,
explicitly documented profile. Khash resizing remains blocked by floating-point
arithmetic. See that example's scope table before interpreting its comparisons
or CBMC results.

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
| Globals/statics and initialization | Persistent addressable globals/statics with constant scalar, array, string and struct initializers; nonconstant initialization rejected |
| Direct calls, recursion, mutual recursion | Implemented with a Lean call stack |
| Indirect/variadic calls, unknown externals | Unimplemented |
| External malloc/free | Executable heap model, failure/success, arbitrary initial bytes, bounds and lifetime checks |
| Allocation primitive, loaded malloc/free/calloc/realloc bodies | Implemented with CBMC failure policies, zero initialization and imported checks |
| Imported end-of-program leak checks | Executed in the translated startup wrapper |
| Variable-length arrays, remaining allocation mechanisms | Unimplemented |
| Byte extract/update | Little-endian eight-bit operations on supported byte layouts; partial extracts retain arbitrary missing bits |
| Bitfields and remaining value operators | Incomplete |
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

Large models use named function bodies and straight-line prefixes to reduce Lean
declaration size. Prefixes split only between GOTO instructions and pass the same
locals through ordinary `Action` binds. They do not introduce PCs, change fuel
counts, simplify conditions or remove checks; small models remain inline.

Little-endian eight-bit byte extract/update reuse the same packed bit layout.
An extract crossing an object's value boundary retains known bits and chooses
the unavailable bits; it does not silently zero-fill. Updates follow the pinned
backend's distinction: a constant offset requires the truncated field to fit,
while a variable offset clips at the end. Negative variable offsets leave updates
unchanged. Byte operators do not imply memory-safety checks. CBMC constant-expression
oracle cases and partial/variable-offset Lean replays cover this slice; big-endian
operators and layouts that disagree with packed byte storage remain rejected.

## CBMC options audit (6.11.0)

This inventory groups the pinned `cbmc --help` and `goto-instrument --help`
options by what they change. It is not a claim that every combination works.
`goto-lean` currently accepts only an input, `--function`, `--object-bits` and `-o`, plus help/version.
Checks must already be present in its GOTO input; passing a check flag to a
separate CBMC run does not insert that check into the translated program.

| Option family | Translation status / responsibility |
| --- | --- |
| Preprocessing, includes, defines, C/C++ dialect, signedness, compiler selection | Upstream frontend options. Supported only when their resulting types/instructions are supported; C++ as a whole is not covered. |
| Architecture, OS, data model (`--32`, `--64`, `--LP64`, etc.), endianness | Recover ABI from GOTO symbols. Little-endian 32/64-bit cases tested; big-endian memory rejected. Other targets are not certified by accepting their ABI. |
| `--function`, input-tree depth limits, `--model-argc-argv`, generated harnesses | Entry/harness selection changes the claim. Translate the selected wrapper to include its assumptions and initialization; arbitrary generated harnesses are not covered. |
| `--object-bits` | Explicit override validated against the input ABI, emitted in Lean and recorded by receipts; 32/64-bit cases tested. |
| Safety instrumentation | Specific coverage in the table below. An assertion is supported only if its expressions and effects are supported. |
| `--add-library`, `--no-library`, malloc failure flags | Loaded reachable bodies take precedence; tested allocation policies described below. Unknown external calls are rejected; not all CBMC library bodies translate. |
| `--nondet-static`, volatile models, MMIO, ISR and function hooks | Resulting GOTO only; no blanket coverage. Nonconstant global initialization and interrupt/concurrency semantics remain gaps. |
| Inlining, pointer removal, slicing, dropping functions, replacing/removing calls or bodies | Explicit upstream transformations only, with no general conformance claim. Function-pointer elimination may produce supported direct calls; indirect calls themselves remain unsupported. Removing a body/check or adding `assume false` can erase obligations. |
| Contracts (`--dfcc`, loop contracts, enforce/replace-call-with-contract), loop havoc/acceleration, k-induction | No established end-to-end coverage. Havoced/transformed code proves a claim about that input; replacement contracts require justification. Do not use options advertised as unsound, such as disabling contract side-effect checks, as evidence of source safety. |
| Threads, weak memory (`--mm`), race instrumentation | Unsupported. |
| Coverage/test generation (`--cover`, failed-assertion coverage) | No end-to-end coverage; reachability goals differ from safety assertions. |
| BMC exploration (`--paths`, unwind/depth limits, incremental loops, complexity limits, field sensitivity, caching) | CBMC search controls, not Lean proof parameters. Search bounds/path abandonment do not establish unbounded safety. If loops are unwound in GOTO, Lean sees the transformed program. |
| SAT/SMT choice, solver processes, refinement, array encodings, formula dumps/statistics | No corresponding printer feature needed for solver selection. String abstraction/refinement and printable-string restrictions have no established translation coverage; floating-point remains unsupported. |
| Property selection, stop-on-fail, traces/witnesses, localization, reports, IR dumps/validation, XML/JSON, verbosity | Upstream diagnostics/selection; do not change what a Lean theorem proves. Property selection can narrow the CBMC comparison. Exporting symex-ready GOTO is not a certified translation pipeline. |

Safety-check coverage distinguishes exercised instrumentation from merely having
the necessary value operators. The positive/negative suites exercise particular
C examples, not every shape a flag can produce.

| Instrumentation flags | Evidence / gap |
| --- | --- |
| `--bounds-check`, `--pointer-check` | Positive/negative imported checks in examples and memory tests. Subobject/alignment coverage is not complete. |
| `--signed-overflow-check`, `--div-by-zero-check`, `--undefined-shift-check` | Positive proofs and deliberate violations in `examples/checks` and `examples/violations`. |
| `--memory-leak-check` | Positive/negative startup-wrapper execution certificates and CBMC controls; not universal Lean leak-freedom proofs. |
| `--unsigned-overflow-check`, `--pointer-overflow-check`, `--conversion-check`, `--enum-range-check` | Paired imported-property certificates and CBMC controls in `tests/options.py`; specific addition, pointer arithmetic, narrowing and sparse-enum cases. |
| `--memory-cleanup-check` | Paired controls for the loaded `exit` body. Its good execution reaches the model's `assume false`, explicitly certified as a rejected path, not a normal return or universal safety proof. |
| `--pointer-primitive-check` | Default instrumentation exercised by memory tests; not an exhaustive pointer-primitive suite. |
| `--float-div-by-zero-check`, `--float-overflow-check`, `--nan-check` | Floating-point gap. |
| `--retain-trivial-checks`, `--error-label` | Ordinary resulting assertions should fit; no dedicated flag-level coverage. |
| `--uninitialized-check`, `--stack-depth` (goto-instrument) | Not established. Arbitrary stable initial bytes alone do not diagnose uninitialized reads. |
| `--no-standard-checks`, individual `--no-…-check` switches, `--no-built-in-assertions`, `--no-assertions`, `--no-assumptions`, `--assert-to-assume` | Change the obligations/path domain. The printer cannot recover checks omitted upstream; assertions converted to assumptions are no longer proved. |

`--object-bits N` must match the comparison CBMC run. The GOTO loader selects
language defaults rather than recovering a custom split. For a 64-bit pointer,
8 object bits leave 56 offset bits; 16 leave 48. The printer uses CBMC's own
`update_max_malloc_size` to align `__CPROVER_max_malloc_size` and startup
initialization with `2^(offsetBits - 1)`, including when using the default split.
The generated header records the choice. Verification policies may set
`"object_bits": 12` (default 8); changing it invalidates the receipt.

`tests/options.py` checks the named imported violations in Lean and CBMC, using
kernel reduction rather than native proof evaluation. It also checks nondefault
32/64-bit splits, the allocation limit, output preservation on invalid options,
and finite-ID exhaustion. The latter is a model-capacity failure, not a C bug.
The tests cover examples, not all programs produced by these flags.

Next gaps include uninitialized-read instrumentation, nonconstant/pointer-valued
static initialization, remaining library operations and layouts, and allocation
identity/reuse. Solver/UI switches do not advance executable GOTO coverage.

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
defaults to eight for C/C++ and accepts `--object-bits N`. Zero and one are reserved for null
and invalid objects. Offset arithmetic preserves object bits, scales by CBMC's
element byte size and wraps within the offset field. As in CBMC, ordered
comparisons between distinct objects return false and their pointer difference
is nondeterministic. A one-past address may be formed but not dereferenced.

This is a first executable memory model, not full CBMC memory compatibility:

- Memory requires little endian, eight-bit bytes and layouts where packed value
  bits agree with object bytes. Mixed-width pointers, non-byte fields and layout
  mismatches are rejected. Taking a parameter's address is not implemented yet.
- Each allocation uses a fresh object ID; released IDs are never reused. The
  default eight-bit ID field has 256 encodings, with two reserved. It can be
  exhausted, including by repeated declarations in loops. The resulting model
  capacity check is not an imported C memory-safety violation. IDs follow this model's allocation order; a
  correspondence with CBMC's numbering, including pointer/integer casts, is not
  established. Allocation identity/reuse and provenance need further comparison
  before claiming unbounded loop/recursion compatibility.
- Loads/stores add explicit object-lifetime and whole-object bounds checks.
  Failure sites end in `memory read` or `memory write`; these checks are additions
  to raw GOTO, not imported source assertions. Their witnesses refute the Lean
  safety model. CBMC separately confirms the corresponding C memory errors.
  Subobject bounds, alignment, effective types and the other C safety obligations
  still require instrumentation and/or further memory-model work.
- Ordinary globals/statics with constant scalar, fixed-array, string and struct
  initializers (including implicit zero initialization) have persistent shared
  byte objects. They are allocated lazily on first access, retaining identity and
  contents across calls/returns. This changes allocation order relative to CBMC;
  numerical pointer identities are not certified. Padding/layout restrictions
  still apply. Pointer-to-object initializers and nonconstant initializers remain
  unsupported. CBMC metadata globals retain their value-only representation;
  taking their addresses is rejected. Const qualification alone does not add a
  read-only memory check. Variable-length arrays remain unsupported.
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
compatibility. The external stubs do not implement CBMC's allocation failure
modes/limits or new/delete bookkeeping. Use loaded library bodies for those policies.
Loaded `realloc` and inserted leak checks are covered below. These explicit C
library models do not establish equivalence to every CBMC built-in implementation. `tests/Calls.lean` includes kernel-checked
recursive execution and callee/library failures, plus a general `vcgen` memcpy
frame proof. General modular function-contract rules and universal parser
invariants remain proof-interface work.

### Loading CBMC's heap model

Compile/link with an entry point (omit `-c`), then use `goto-instrument --add-library`
with the desired allocation-failure options before printing. The library linker follows
calls reachable from the entry; adding the library to an entryless object need not load
any bodies. Include `--pointer-check --bounds-check` to retain memory-safety properties.

The printer now handles the `allocate(size, zero)` side effect, dynamic-object tests,
and r/w/rw_ok predicates (including their prophecy forms). The allocator always succeeds;
the **loaded C library** controls failure, maximum size and bookkeeping. Its zero flag
selects zero bytes without an arbitrary-byte choice, or stable arbitrary initial bytes.
CBMC uses the pointee extent for typed allocations and the size operand for void pointers;
the printer follows that distinction using CBMC's layout information.

Loaded `__CPROVER_deallocate` executes unchanged: it nondeterministically records a
pointer in `__CPROVER_deallocated`. It does **not** erase bytes. Imported checks can
therefore witness a deallocated object, while another monitoring choice may miss it on
one replay. Successful replay is not universal safety. The external `free` stub instead
invalidates every freed object; the two paths deliberately expose different models.

Loaded `realloc` now uses a Lean model of `__CPROVER_array_copy`. It preserves the
common byte prefix, truncates on shrink, and chooses fresh arbitrary extension bytes
on growth. This first array-copy slice requires live **base pointers**, not interior
or subobject views. The unmodified library body handles allocation failure, null,
zero-size requests and freeing the old object. Logical `&&`/`||` operands with effects
are evaluated only when needed; shrinking must not read a guarded-away old extent.

`tests/heap-library.c` and `tests/HeapLibrary.lean` cover these cases and named
counterexamples for stale pointers, assumed-zero extensions and array-copy padding.
The memory runner compares the C properties against CBMC and audits Lean certificates.
Positive Lean execution certificates are concrete; they are not universal realloc proofs.

For leak checking, add `--memory-leak-check` during instrumentation and translate
`__CPROVER__start`, not just the C entry function: CBMC puts the final leak assertion
in that wrapper. `tests/leaks.c` uses void, argument-free entry functions to avoid the
startup trace I/O instructions, which remain unsupported. For example:

```sh
build/bin/goto-cc --function leak_bad tests/leaks.c -o build/memory/leak-raw.gb
build/bin/goto-instrument --add-library --malloc-may-fail --memory-leak-check \
  --pointer-check --bounds-check build/memory/leak-raw.gb build/memory/leak.gb
build/bin/goto-lean build/memory/leak.gb --function __CPROVER__start -o build/memory/Leak.lean
```

The runner verifies that the actual `__CPROVER__start.memory-leak.1` property was
inserted. `tests/LeakSafe.lean` certifies a returning whole-program execution;
`tests/LeakUnsafe.lean` certifies that losing the allocation reaches that property
and refutes safety. Both explicitly enable the allocation monitor; CBMC separately
checks the good entry for all choices and finds the leak in the bad one. The two
startup modules are checked separately because they use the same namespace.
Successful individual monitoring choices do not establish universal leak freedom.

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
broader static initialization, more string/numeric library operations and floating point.
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
