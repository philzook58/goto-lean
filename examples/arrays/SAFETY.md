# Instrumented safety checks

Run `make checked checked-cbmc` here. The upstream C copies remain unchanged.
`scale_cbmc.c` contains the readable C assumptions and functional assertions.

The check policy is explicit: `--pointer-check --bounds-check
--signed-overflow-check --div-by-zero-check --undefined-shift-check`.
This is not every optional CBMC check (for example unsigned overflow,
conversion, pointer arithmetic overflow and floating-point policies are excluded).
`goto-instrument` inserts assertions before either tool sees the program.
`Checked/*.lean` retains their property IDs and original source locations;
`.lake/verification/properties.json` lists the actual inserted algorithm properties.
Flags do not imply a property was needed or inserted in every algorithm.

| Algorithm | Instrumented Lean replay cases | CBMC C assertion harness |
| --- | ---: | --- |
| lower_bound | 860 (shared with reverse) | All inputs, length ≤ 4 |
| reverse | 860 (shared with lower_bound) | All inputs, length ≤ 4 |
| fill | 765 | All inputs, length ≤ 4 |
| find | 765 | All inputs, length ≤ 4 |
| is_sorted_until | 153 | All inputs, length ≤ 4 |
| rotate | 454 | All inputs, length ≤ 4 |
| bubble_sort | 153 | All inputs, length ≤ 4 |

All passed. There are 3,150 input rows across the two replay suites, compared
with native C and independent Python results. They include empty arrays,
duplicates, signed extrema, sentinels and nonzero pointer offsets; some arrays
are longer than the CBMC bound. A failed check causes replay to fail.

`safety.py` checks each C harness separately with arbitrary 32-bit values and
lengths up to four, plus every inserted check and unwinding assertions. Full
logs are under `.lake/safety/`. CBMC's output also lists properties in uncalled
functions, so its total property count is not a count of exercised properties.
Each algorithm has its own reachable harness run. The unwind bound is six.

`CheckedExecutions.lean` has a kernel-checked successful execution certificate
for each instrumented algorithm, and a failure certificate showing that setting
CPROVER's dead-object global actually triggers the imported check. These are
concrete certificates, not universal safety proofs. No native-checking axioms
are used (the audit reports only `propext` and `Quot.sound`).

`Spec/CheckedFill.lean` and `Proofs/CheckedFill.lean` now establish **unbounded
safety, functional correctness and termination of instrumented fill**, including
all six imported pointer properties and the memory-model store check. The theorem
quantifies over every unsigned 32-bit length and value under explicit readable
array, nonwrapping offset and object-state preconditions; it assumes no fixed
unwind limit. Its completion bound is `2*(length+2)` generated blocks. Empty fill
also has a separate theorem allowing a null pointer with arbitrary memory.

`Spec.lean` and `Verified.lean` describe the seven universal contracts for **raw**
translations. The remaining six algorithms do not yet have universal proofs of
the added CBMC properties. The bounded C assertion harnesses likewise are not
universal Lean harness proofs. `examples/checks/Proofs.lean` separately proves all
five small C assertion examples, including their inserted checks, universally.

The instrumented fill proof runs in the default `lake build` and `make checked`.
It checks `verify`, `implements`, `safe` and `empty` with `#check_axioms`, permitting
only `propext`, `Classical.choice` and `Quot.sound`. The actual assertions stay in generated code;
no new assumptions or simplifications were added to the translator.
See [FILL_EDITS.md](FILL_EDITS.md) for the first measured proof-repair experiment.

The translator now supports value-only globals with constant scalar initializers
(including implicit C zero initialization), shared across calls and memory writes.
It reads/writes CPROVER's actual global symbols; it does not replace their checks
with assumptions. Address-taking of globals and heap allocation remain unsupported.
Object size is exact for live modeled objects; sizes of unavailable/dead objects
are unconstrained because the current memory model discards their old extents.
That is an overapproximation, not an exact model of all object-size queries.

The checked translations and named claims have a [local Lean receipt](../../docs/RECEIPTS.md).
`verification.json` labels fill's scope as unbounded and the other six as concrete
executions. `make status` rechecks artifact identity. Raw universal claims and the
separate bounded C/CBMC harnesses are not included in this checked receipt.
