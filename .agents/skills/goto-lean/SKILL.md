---
name: goto-lean
description: Translate C through CBMC GOTO into Lean, replay executions, prove instrumented properties, and certify counterexamples with goto-lean.
---

# goto-lean

Work in the goto-lean checkout. Translate with
`python3 tools/translate.py input.c --function entry --out build/task`.
Keep C, its checks, and generated `Model.lean` unchanged while proving;
write handwritten work in `build/task/Spec.lean`.

Read the matching section of `docs/AGENT_GUIDE.md`: replay, finite completion,
loop invariants, or failures. Inspect the generated signatures and PCs first.

Choose the public claim to match the request:
- `eval`: one input and choice stream.
- `Executes`: one possible execution.
- `run ... .wp Q`: universal safety and partial correctness; permits divergence.
- `finishes step fuel initial Q`: universal completion within a block bound,
  under source assumptions. It has no choice-list argument.

Use `simp` with the starter's local reduction rules; `simp only [step]` omits
those rules. Then inspect the residual goal (`trace_state`).
Introduce only the binders that remain there; simplification can eliminate
overwritten declarations, so counting C declarations gives the wrong context.
When only arithmetic remains, work on that goal instead of unfolding `step`
again. Prove the requested scope before attempting optional stronger claims.

Export a named `finishes` theorem when completion is requested, even if also
proving a `.wp` corollary. Retain exact property sites for bug witnesses.
Do not add assumptions, axioms, `sorry`, or weaken the requested property.
This is a Std project. `bv_decide` in pinned Lean 4.35.0 can add native axioms
rejected by the existing audit; use kernel-checkable reasoning for final claims.

After the final edit, compile and audit every public theorem:

```sh
python3 .agents/skills/goto-lean/scripts/check_spec.py --project build/task --completion-claim completes
```

Use `--claim` for other theorem types, `--replay-only` for concrete-only work.
Report the actual result and remaining obligations. Translation alone proves no
assertions, and a passed audit does not establish agreement of the model with C.
