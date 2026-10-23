# What a green result means—and can leave wrong

A proof establishes **a particular property of a particular Lean model, under
particular assumptions**. We still need to justify the property, assumptions,
model and connection to deployed code.

For any result, record the **claim, program/configuration, admitted inputs,
evidence and remaining trust**. Read the C and theorem header before the tactics.

## A proved property can miss the requirement

A function returning zero satisfies `result >= 0`. Sorting without permutation
can allow replacing every element with zero. Bounds safety does not establish
that a parser recognizes the intended language.

Our array [`Frame`](../examples/arrays/Spec/Array.lean) describes final bytes: a
write outside the array followed by restoration is permitted. It does not prove
absence of intermediate writes or preservation of all memory metadata. Current
contracts imply no timing, constant-time, resource or concurrency guarantee
unless explicitly stated.

**Improve:** review contracts against intended and forbidden examples. Include a
wrong implementation that the specification rejects. Review changes to assumptions
and contracts when repairing proofs; weakening the claim is not the same success.

## Assumptions can remove the bug—or every execution

```c
__CPROVER_assume(x > 0 && x < 0);
__CPROVER_assert(0, "unreachable");
```

A universal proof can succeed without a successful execution. Less obvious
assumptions can exclude the boundary input that matters. Placement matters too.
[`Action.wp`](../GotoLean/Basic.lean) treats an assumption as an implication,
but requires a check to be true. Even [`finishes`](../GotoLean/Termination.lean)
permits assumption rejection: it does not establish that feasible inputs exist.
Our signed-add example intentionally excludes INT_MAX; a caller must respect that.

**Improve:** provide feasible positive executions, exercise important boundaries,
and prove actual callers establish preconditions. One witness rules out a wholly
empty domain, but does not show that all necessary production inputs are admitted.

## Different kinds of evidence have different scopes

| Result | What remains unproved |
| --- | --- |
| Generated Lean compiles | Any assertion holds |
| A returned replay or `Executes` witness | Other inputs or choices are safe |
| `run ... .wp Q` | Termination: a forever-loop can satisfy a false return postcondition |
| `finishes` for admitted inputs | Those inputs exist or describe realistic callers |
| Bounded CBMC success | Behavior beyond the bounds; inspect unwinding assertions |
| A named failed check in Lean | Correspondence to a failure in the original C |

[`Outcome.Satisfies`](../GotoLean/Exec.lean) is intentionally true for exhausted
fuel, missing/invalid choices and rejected assumptions. Its soundness theorem is
not a successful-return certificate. Positive certificates require an actual
returned witness. [Existing tests](../tests/Semantics.lean) demonstrate assumption
vacuity and a forever-loop satisfying a false return postcondition.

“Unbounded” means no chosen loop-unwinding limit, under the stated machine widths
and memory premises. It does not mean infinite-sized C objects or all C features.
[The example table](../README.md#what-is-established-today) distinguishes raw
proofs, instrumented proofs, bounded harnesses and concrete certificates.

## Missing assertions and mismatched artifacts

Bitvector arithmetic has results where C can have undefined behavior. Wrapping
addition or the model's nondeterministic division by zero does not establish C
safety. The required checks must be inserted and included in the proved program.
Our five selected instrumentation flags are not every optional CBMC check.
Bounds instrumentation alone can add nothing for pointer-indexed array bodies.
`True` as a postcondition can be useful with the intended checks present, and
very weak without them. CBMC's counts also include unreachable properties;
those totals are not coverage. The uninitialized-value pair tests a source
assertion, not blanket detection of uninitialized reads.

A proof may concern old generated Lean, another entry point, different headers,
macros or ABI. Source/property labels help navigation but do not authenticate
source contents. Example Makefiles regenerate inputs; `lake build` alone does not retranslate
edited C. The checks, checked-array and violation examples now have
[local receipts](RECEIPTS.md) binding inputs/configuration and actual properties
to named checked Lean claims. Other workflows are outside this receipt mechanism.

**Improve:** bind the result to its source/configuration and generated artifacts;
review the actual property inventory against the intended claim. Report omitted,
unsupported and unproved checks. A removed assertion must change the claimed scope.

## The translation and memory model remain trusted

```text
C + headers + flags → CBMC frontend/instrumenter → GOTO → C++ printer → Lean model
                                                                            ↓
                                                               kernel-checked theorem
```

We have no machine-checked simulation of these translations or of the model
against CBMC execution. A wrong branch, cast or access can print valid Lean.
Native expressions simplify the implementation; they do not prove its mapping.

Concrete [memory-model limits](../COMPATIBILITY.md#first-object-memory-slice):

- Pointer width follows the input ABI; object-bit width uses the printer's default
  CBMC configuration. A differently configured CBMC run can use another encoding.
- Allocation IDs follow this model's order, are never reused and can exhaust in
  loops. Pointer/integer casts can expose identity differences from CBMC.
- Whole-object bounds and liveness do not establish general alignment, subobject
  or effective-type obligations.
- Dead extents are discarded; unavailable sizes become arbitrary choices. That
  local overapproximation does not prove the whole model conservative.
- [`memcpy`/`strlen`](../GotoLean/Library.lean) are explicit library models, not
  equivalence proofs. Copying is atomic and rejects null/dead pointers even at zero length.

Some differences cause false alarms; not all differences have been classified
or proved conservative. Unsupported constructs fail explicitly, but accepted
constructs can still contain implementation errors. Fill's `ObjectState` is a
caller obligation, not proof that a real caller provides consistent metadata.

**Improve:** prioritize memory conformance and an explicit simulation relation.
Native-C comparisons, CBMC oracles and negative controls provide evidence, not
semantic equivalence. Proof and replay share definitions and possible mistakes;
CBMC comparisons share the frontend/instrumenter. Native C is not a reliable
oracle on undefined executions. A model counterexample can be spurious relative
to C until correspondence is established.

## Axiom checks help, within a limited scope

The kernel checks proofs relative to their axioms. Successful Lean compilation
alone can admit `sorry` or a custom axiom. Our named audit commands now enforce:

```lean
import GotoLean.Audit
#check_axioms MyProof.safe
```

Only `propext`, `Quot.sound` and `Classical.choice` are allowed, using Lean's
transitive dependency information. Unexpected dependencies and unknown/ambiguous
names fail compilation; passing checks are quiet. Existing audit lists and
certificate checks use this gate. It audits the **named declarations**, not every
possible claim, specification adequacy, model fidelity or the build toolchain.
An unaudited declaration can still compile. The regression tests deliberately
exercise imported custom axioms and `sorryAx` to ensure rejection.

There is no verified transfer to a production binary, compiler configuration,
hardware or I/O environment. A fast proof check also does not measure proof
construction or maintenance effort.

## Next steps

The axiom gate and scoped [artifact receipts/inventory checks](RECEIPTS.md) are
implemented. Receipts detect stale/mismatched inputs and missing expected checks;
reviewed scope labels and category counts do not prove specification adequacy or
translation correspondence. The remaining work is proposed, in this order:

1. **Broaden caller coverage.** The four-element caller in `examples/arrays/caller.c`
   now establishes checked fill's premises and proves its source assertion for every
   input value, with a certified underfill failure. Extend beyond its fixed capacity
   and empty initial modeled memory. Start with allocating an array and calling checked
   fill. Discharge its readable-array, nonwrapping and metadata premises; check
   the resulting C assertions. Require feasible positive controls and intended
   negative controls. Contradictory assumptions must never count as a returned case.
2. **Targeted conformance.** Compare allocation/lifetime, pointer casts/offsets,
   layouts, object-size and library effects with pinned CBMC, using its interpreter
   where appropriate. Deliberately wrong mappings must be detected. Classify each
   discrepancy for a stated domain; constrain or reject unresolved cases before
   making dependent claims. Extend other instrumented proofs with small reusable lemmas.
3. **Scoped translation correspondence.** Write down a simulation and prove a
   scalar slice before designing general translation validation. A mistranslated
   branch/cast must fail a checked correspondence certificate. State the remaining
   trusted decoder and frontend boundary; a second interpreter produced by the
   same faulty mapping is not independent validation. Extend to memory after its
   object/provenance relation is clear. Production-binary assurance is a later boundary.

Each step needs a positive example and a deliberate failure. Keep the readable
contract and actual checked evidence central; add machinery only when a concrete
example shows it prevents a misleading result or simplifies verification.
