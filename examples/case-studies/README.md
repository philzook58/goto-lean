# Three small real-code case studies

Read the checks in the C wrappers first. They call unchanged, attributed sources;
the generated Lean is disposable. [SOURCE.json](upstream/SOURCE.json) pins files,
authors, licenses and the collection revision. The collection itself contains
adaptations, so these are not claimed to be pristine original-project releases.

| Read | Property and scope |
| --- | --- |
| [json.c](json.c) | Fresh jsmn parser; at most 8 input bytes and 4 tokens. Counts and successful token spans are consistent. This is tokenization, not full JSON validation. |
| [slide.c](slide.c) | Original 2048 row move, with score initially zero. Move flag, tile mass and a named once-per-move merge example. Bytes encode exponents: 0 is empty, 1 is tile 2. |
| [lookup.c](lookup.c) | Every 32-bit lookup key in one explicit four-bucket table containing a collision chain and tombstone. No allocation/resizing claim. |

From this directory, after the normal repository build:

```sh
make check  # regenerate; native/Lean comparisons; initialization and violation proofs
make cbmc   # also check named positive/negative controls, including unwinding
make fuzz   # optional Clang/libFuzzer: 5,000 native inputs with ASan/UBSan
```

`check.py` compares 268 JSON reports (all token and parser fields), 1,137 row/score
results, and 261 lookups across four modes. Rows cover every combination of
exponents 0..4 plus seeded samples in 0..15. An independent compact-then-merge
Python specification checks row/score results. Named JSON cases assert expected
return codes, including malformed input and exhausted token capacity.
Reports and replay inputs are under `.lake/check/`. `Run.lean` reads the same
input protocol as `native.c`; errors/rejected/exhausted runs abort comparisons.
These concrete agreements are not universal Lean proofs or a translation-equivalence theorem.
All three comparison models import CBMC bounds, pointer, signed-overflow, division
and shift checks. The jsmn model retains 848 property IDs, including 822 pointer
checks, in this pinned example.

## Positive proof

[Spec.lean](Spec.lean) states the initialization contract;
[Proofs/Init.lean](Proofs/Init.lean) proves it over the full instrumented `jsmn_init`.
For arbitrary initial parser bytes, initialization completes, sets `pos = 0`,
`toknext = 0`, `toksuper = -1`, and preserves every byte outside the parser.
All 18 imported pointer checks and the model's three store checks are included.
The stated standalone layout places the parser at object 2, offset 0, with an
arbitrary unrelated object and arbitrary trailing bytes. This is a helper contract,
not a theorem about the parsing loop or every possible caller heap.

The proof composes memory-operation contracts instead of reducing all byte-array
updates together. It adds one disjoint-store lemma to the proof library; the
execution model and C++ printer are unchanged.

## What the negative cases tell us

- **Wrong API expectation:** `truX` is accepted by this non-strict jsmn tokenizer.
  The fixed corpus has 114 non-error results rejected by Python's JSON decoder,
  including empty/incomplete/non-JSON inputs. Do not equate a token count with
  JSON validation. The deliberately wrong caller assertion fails in CBMC and Lean.
- **Actual undefined behavior:** merging exponent 31 tiles shifts a 32-bit score
  value by 32. UBSan, CBMC and Lean all detect it. The input is outside the positive
  test range; reachability from normal interactive gameplay has not been proved.
- **Weak specification:** removing 2048's merge barrier still passes CBMC's tile-mass
  property. The stronger named merge example catches it in CBMC, native execution,
  and Lean. A mass-only proof would miss incorrect gameplay.
- **Deleted is absent:** the intentionally wrong claim that a deleted key remains
  present fails. The positive lookup property checks the tombstone collision chain.

[Violations.lean](Violations.lean) contains four kernel-checked refutations of the
corresponding generated `run.wp` safety claims. `#check_axioms` rejects holes and
native-checker axioms. Each proof checks the exact expected property site, so an
unrelated failing check cannot stand in for the named violation. These certify
named counterexamples, not a universal repair.
The JSON certificate retains its earlier bounds/arithmetic instrumentation:
kernel replay with the full pointer profile still exceeds 1 GiB. Its generated
module is `JsonClaim`; the full comparison model is `Json`. CBMC's negative
control uses the full profile. A lighter replay certificate does not prove that
all the additional pointer checks succeed before the caller assertion fails.

## Boundaries that matter

CBMC proves the small-exponent mass property and fixed-table lookup for all
admitted inputs, with unwinding assertions. Its eight-byte symbolic JSON query
exhausted our 1.5 GiB budget: **that domain remains unproved**. Resource errors and
incomplete checks are not passing results. A harness compilation mistake initially
asserted caller limits instead of assuming them; `-D__CPROVER__` fixes that distinction.

The full jsmn translation previously put about 17,000 lines in one dispatcher
and failed Lean elaboration/kernel checking. The printer now names function bodies
and straight-line prefixes in large models. This changes declaration boundaries;
it preserves checks, instruction order, PCs, choices and fuel accounting. The full
model compiles and runs with one thread and `-M1024`, with about 2% more source.
This fixes loading/execution, not the kernel-replay limitation above.

The khash resize probe fails translation on `floatbv` in its load-factor arithmetic.
Lookup support is not general heap/hash-table support. Fuzzing tests native C's
selected properties, with slide exponents restricted to 0..15; it is not a proof
or lockstep Lean fuzzing. Corpus/crash artifacts stay under `.lake/check/`.

The next proof-scaling task is checking full-profile traces in small pieces,
rather than reducing a whole parser execution in one proof.
