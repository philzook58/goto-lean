# A verified token parser

This example contains the C input, generated Lean, handwritten contracts and
proofs, and a concrete execution. It needs no sibling repository or custom
`LEAN_PATH`. `take_word.c` contains locally written `take_word` and `copy_word`
repair helpers from the Cornell serial-assurance experiment; see [attribution](SOURCE.md).
The small `main` keeps those static functions in the
GOTO object. The proof selects `take_word` as its entry.

From the goto-lean repository root, build the tools once:

```sh
cmake -S . -B build
cmake --build build --target goto-lean-tools -j2
```

Then translate, check the proofs, and run the example:

```sh
cd examples/parser
make generate
lake build
lake env lean --run Run.lean
```

`make check` performs these steps and enforces the proofs' transitive axiom policy.
`GOTO_CC` and `GOTO_LEAN` can name other
tool builds. Edit `take_word.c`, regenerate, and rebuild to recheck the proof
against the changed program. Handwritten files stay separate from generated files.

The execution copies `hi` from `"  hi there"`, appends NUL, preserves the rest
of the output buffer, and advances the cursor to byte 5. It also checks the
result against the proved functional specification.

[`Cases.lean`](Cases.lean) adds twenty named inputs: empty/space-only strings,
capacity boundaries, multiple words, tabs/newlines and UTF-8 bytes. It proves the
`Ready` memory premises, NUL termination and a completed execution for every row.
An ordinary parse failure returns 0; it is not an `assumptionRejected` path.
`make check` runs the exact same rows against compiled C and compares results,
cursor offsets, unchanged input and every output byte. These are feasibility and
differential checks, not complete input coverage.

## Reading the proof

- [take_word.c](take_word.c): the program being verified.
- [Generated/TakeWord.lean](Generated/TakeWord.lean): executable blocks, source
  references, and named pointer-layout constants. No CFG folding or source inlining.
- [Proofs/Scan.lean](Proofs/Scan.lean): an executable sequence specification. NUL
  termination proves that all three scans stay within the supplied bytes.
- [Proofs/CopyWord.lean](Proofs/CopyWord.lean): a reusable contract for the actual
  helper, including copied bytes, NUL and a byte-level frame condition.
- [Proofs/TakeWord.lean](Proofs/TakeWord.lean): loop annotations and their connection
  to the generated `run`. `verify` gives the exact result and memory; `success`
  gives the readable `Parsed` contract; `rejected` establishes unchanged memory.
- [Run.lean](Run.lean): a client proof using the successful-return
  contract, plus initial-memory setup and concrete execution.
- [Audit.lean](Audit.lean): explicit axiom reports, kept separate from normal builds.

The universal theorem covers any NUL-terminated byte sequence under `Ready`:
64-bit pointers with 56 offset bits, separate live input/output/cursor objects,
a readable input slice, a cursor containing its initial address, sufficient
output capacity, and explicit bounds excluding pointer-offset wraparound.
It includes empty words and insufficient capacity, which return zero without
changing memory. Input pointers may start inside their objects. Bytes after the
first NUL are irrelevant to the scans.

Success proves the word contents, terminator, updated cursor, unchanged input,
unchanged bytes outside the writes in the output and cursor objects, and a frame
for every other object. The result is unbounded safety and partial correctness;
termination and correctness of the C-to-GOTO-to-Lean translation are separate.
The proofs use only standard Lean axioms, with no holes or native-checker axioms.
