# What a green result means

Lean checks a theorem about the translated model, under its stated assumptions.
It does not establish that the theorem expresses the requirement, that every
intended input is admitted, or that the translation matches the deployed C.

## Read the claim first

| Evidence | What remains open |
| --- | --- |
| Generated Lean compiles | No program assertion has been proved. |
| A replay returns the expected value | Other inputs and nondeterministic choices. |
| `Executes` | One possible execution, not universal safety. |
| `run … .wp Q` | Termination; a diverging program can satisfy a false return postcondition. |
| `finishes` | Whether the admitted inputs exist and describe realistic callers. |
| Bounded CBMC success | Behavior beyond the checked bounds; inspect unwinding assertions. |
| A named failed Lean check | Whether that model execution corresponds to the original C. |

`Outcome.Satisfies` accepts fuel exhaustion, choice errors and discarded
assumptions. Its soundness theorem is not a successful-return certificate.
Require actual returned witnesses for positive executions.

## Common sources of false confidence

- **Weak specification.** A property may omit behavior that matters. The 2048
  mutation in the [case studies](../examples/case-studies/README.md) preserves tile
  mass while merging incorrectly. Test a plausible wrong implementation.
- **Vacuous assumptions.** Preconditions can remove the bug or every execution.
  Keep feasible callers and boundary witnesses. Witness tables do not prove that
  every intended production input is admitted.
- **Missing checks.** Bitvectors define some operations for which C has undefined
  behavior. Prove the instrumented input, inspect its properties, and report omitted
  flags. `True` is useful as a postcondition only when the checks express the claim.
- **Stale or different inputs.** Lean does not retranslate edited C. Entry, headers,
  macros, ABI and flags matter. [Receipts](RECEIPTS.md) bind supported example claims
  to current artifacts; source labels alone do not authenticate them.
- **Unreviewed axioms.** Compilation can admit `sorry` or custom axioms. Use
  `#check_axioms` on every public claim; it permits only `propext`, `Quot.sound`
  and `Classical.choice`. The audit checks named declarations, not spec adequacy.

The [example notes](../README.md#three-examples-to-review) distinguish universal
proofs, concrete certificates and separate CBMC controls. “Unbounded” means no
chosen unwinding limit within the stated machine widths and memory premises.

## The translation remains trusted

```text
C + headers + flags → CBMC frontend/instrumenter → GOTO → printer → Lean model
                                                                     ↓
                                                               checked theorem
```

There is no proved simulation across this pipeline. A wrong branch, cast or
memory operation can produce valid Lean. Tests against native C and CBMC expose
some discrepancies; they do not establish equivalence. Replay and proof share
model definitions; CBMC comparisons share the frontend. Native execution is not
an oracle for undefined behavior.

The [compatibility inventory](../COMPATIBILITY.md) records memory and feature
limits: object IDs and pointer casts, allocation/lifetime policies, unavailable
object sizes, subobject/alignment gaps and explicit library models. Unsupported
constructs are rejected, but accepted constructs can still contain mistakes.
Some model differences can cause false alarms; conservativeness is unproved.
A caller must establish premises such as fill's live-object metadata.

Local receipts are editable build data, not signed attestations or translation
certificates. There is no verified transfer to a production binary, hardware or
I/O environment. Proof-checking time also says little about proof-maintenance cost.

## Next steps

1. Prove useful positive contracts and discharge their premises in real callers.
2. Extend native/CBMC conformance tests, with deliberate failures, as features grow.
3. Establish a scoped translation simulation before claiming end-to-end C assurance.

Keep the contract, admitted inputs, actual checks and remaining gaps visible.
