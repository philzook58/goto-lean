# Unchanged local repair helper

This helper was written in the local Cornell serial-assurance repair experiment;
it is not original Cornell firmware. See [source attribution](../../examples/parser/SOURCE.md).

The actual `cornell-serial-assurance/generated/take_word.inc` and its existing
`harness/check_word.c` now translate and type-check. The selected `take_word`
calls its original `copy_word`, which calls the Lean memcpy model and then writes
the terminating NUL. Its cursor update writes through the caller's `char **`.
The original main harness's strlen calls also translate. No source inlining or
replacement recognizer is used, and no files in the Cornell project are edited.

`run.py` builds the original harness with goto-cc, prints both entry points and
compiles the same helper behind a small native wrapper. It compares 195
input/capacity combinations: success flags, cursor offsets, all 16 output bytes
and unchanged input contents. Cases include empty input, leading/trailing
spaces, insufficient capacity, embedded NULs and bytes above 127. All agree.

`Proofs.lean` kernel-checks a concrete execution on `"  hi there"`: the result
is one, output begins `hi` followed by NUL, other output bytes retain their
initial value, input is unchanged and the cursor advances to `there`. The
execution theorem uses only standard axioms. A second concrete run reaches and
passes the original harness's strlen and cursor assertions.

`examples/parser/Proofs/CopyWord.lean` proves the generated `copy_word` correct for every memory and
argument tuple satisfying `CopyPre`. `CopyPost` states that the first `n` output
bytes equal the original source bytes, the next byte is NUL, and every other
byte is unchanged. Object liveness and extents are preserved too. The
precondition includes readable/writable ranges, separation, sufficient capacity
and a bound excluding pointer-offset wraparound. It also permits an empty copy.

The checked summary quantifies over every postcondition of the generated helper
block. `copy_word_call` verifies its actual call site using only that contract
and the caller's next-block annotation. `take_word_rule` connects caller-block
annotations to the original generated `take_word.run`; the callee proof is
already discharged. `examples/parser/Proofs/TakeWord.lean` now supplies and proves
all three loop invariants and the remaining block obligations. It proves exact
success/rejection results and memory, and a readable successful-return contract
including the cursor, word contents, unchanged input and byte-level frames.
`Proofs/Scan.lean` computes and proves the word boundaries from NUL termination.
Users do not have to supply those boundaries as additional assumptions.

The shared `GotoLean.Contracts.calls_spec` theorem justifies this workflow for
the existing call-stack interpreter, including recursion. Its independent
factorial regression proves a result for every 32-bit input without a
user-written stack invariant. `GotoLean.MemoryLemmas` supplies the byte-copy
and frame laws. All these proofs use only standard Lean axioms, with no proof
holes or native-checker axioms. The C++ printer and executable semantics are
unchanged; proof modules are optional imports.

```sh
python3 experiments/parser/run.py
```

The script needs the sibling Cornell project; standalone CTest does not. Its
generated files remain under `build/parser`. The script checks both the concrete
executions and the universal parser proofs against modules generated from the
local repair harness. The proof assumes separate live input/output/cursor
objects, readable input bytes containing NUL, a valid cursor value, output capacity
and pointer-offset bounds, using the 64-bit ABI. It proves safety and partial
correctness, not termination or the complete command parser. Globals, more
library functions and floating point remain implementation work.

The sibling-free workflow is in `examples/parser`: `make generate`, `lake build`,
and `lake env lean --run Run.lean`. CTest runs it too. Native differential checks
against the external Cornell project remain this purpose-specific script.
