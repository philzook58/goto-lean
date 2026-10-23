# Use your own C

Start with one function and a precise claim. Use CPROVER assumptions for caller
preconditions and assertions for required behavior. Read both before the proof.
An assumption that excludes the interesting inputs can make a claim useless.

## Translate first

From the repository root, for a function `process` in `input.c`:

```sh
mkdir -p build/try
build/bin/goto-cc -std=c11 -c input.c -o build/try/raw.gb
build/bin/goto-instrument --pointer-check --bounds-check --signed-overflow-check \
  --div-by-zero-check --undefined-shift-check build/try/raw.gb build/try/checked.gb
build/bin/goto-instrument --show-properties build/try/checked.gb
build/bin/goto-lean build/try/checked.gb --function process -o build/try/Process.lean
lake env lean -o build/try/Process.olean build/try/Process.lean
```

This last command only type-checks the generated program. It does **not** prove
its assertions. Inspect the actual property list: enabling a flag does not mean
it inserted a check, and this policy does not enable every optional CBMC check.
Pointer-indexed arrays need pointer instrumentation; bounds checks alone may add nothing.
Unsupported reachable constructs produce an error rather than a partial translation.

## Keep three things separate

| File | Read it to answer |
| --- | --- |
| C source | What code, assumptions and assertions do I mean? |
| Generated Lean | What executable model and checks did the tool emit? |
| Handwritten proof | Why do those checks hold, or where can one fail? |

Add a small `Spec.lean` **when it helps** express an overall result, memory framing,
termination or caller memory obligations. Its job is a readable contract; it
should not repeat C assertions unnecessarily. For the simple C-first tutorial,
the assertions already are the specification, so no separate Spec file is needed.

Use `LEAN_PATH=build/try lake env lean YourProof.lean` to import `Process` from a
handwritten harness. Keep proofs outside generated files. Start from the
[small C assertion proofs](../examples/checks/Proofs.lean); for loops, use the
[checked fill proof](../examples/arrays/Proofs/CheckedFill.lean) and existing ranking rules.
This is manual verification with reusable lemmas, not an automatic C-to-proof command.

## Change, regenerate, check

After a C edit, regenerate the instrumented GOTO and Lean, then rebuild the proof.
For the examples, `make check` does this. Repair a failed local obligation rather
than adding an assumption or weakening the contract to make the build pass.
Keep a successful case and a buggy case that certifies the **intended property**.
The checked examples also write [local Lean receipts](RECEIPTS.md); `make status`
rejects stale source/configuration, artifacts or proofs. Their reviewed property
policies must change explicitly if expected coverage changes. `lake build` alone
does not create such a receipt.

Distinguish the result you obtained:

- A returned replay checks one execution; `exhausted` or `assumptionRejected` is not one.
- An `Executes` theorem certifies an execution, not all executions.
- `run ... .wp` proves safety/partial correctness and can allow divergence.
- `finishes` additionally establishes completion, for paths admitted by assumptions.
- A bounded CBMC result is scoped to its bounds; check unwinding assertions too.

The C frontend, printer and memory-model fidelity remain trust boundaries.
Generated Lean's successful compilation is not a proof of translation correctness.
Use the [confidence review](CONFIDENCE.md) when reporting results. Its
[next steps](CONFIDENCE.md#next-steps) distinguish current safeguards from proposed work.

## A short prompt for an AI

> Verify `process` in this C file using goto-lean. Keep the C assumptions and
> assertions as the specification. State any necessary memory preconditions
> explicitly. Generate instrumented GOTO and retain its source/property IDs.
> Keep proof code separate; reuse existing Lean lemmas. Include a successful
> control and a certified failure of a named property in a buggy variant.
> Do not add axioms, leave `sorry`, or weaken the claim to get a green build.
> Report the exact theorem, checked commands, artifact/configuration identity,
> admitted inputs, feasible controls and remaining gaps. Add `#check_axioms` for
> the public claims and report which declarations were audited.
> Call out any changed assumptions or contract rather than claiming the same result.

Judge the result by the C, the contract and the checked theorem header. Proof
length and a confident explanation are not evidence that the intended claim holds.
