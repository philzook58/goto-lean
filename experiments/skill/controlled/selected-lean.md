---
name: lean4-selected
description: Selected Lean proof-development techniques for a Std-only shell environment.
---

# Lean proof work

Adapted from the installed lean4 skill's search-first, incremental-validation,
goal-structure and error-diagnosis guidance. No Mathlib or LSP is installed here.

- Search for existing lemmas before inventing a proof. Locate installed sources
  with `lean --print-prefix`; search `src/lean/Init/Data/BitVec` with `rg`.
  Use `#check`/`#print` in a scratch file to verify names, types and orientation.
- Compile a small step before building on it. Put `trace_state` just before a
  failing tactic to read the actual goal and hypotheses. Repair that goal;
  do not repeat a long chain of speculative tactics.
- Match the goal's structure: `intro` for arrows/forall, `constructor` for
  conjunctions, `refine ⟨witness, ?_⟩` for exists. `apply` takes a proof or
  theorem, not a proposition. Use `change` for definitionally equal wrappers.
- Use `rfl` or `simp` for reduction, `simp_all` to use hypotheses, `omega` for
  Nat/Int linear arithmetic. For BitVec arithmetic, inspect its `toNat`/`toInt`
  lemmas and bounds first. Use `theorem` in Std; `lemma` is a Mathlib alias.
- Remove tactics after a goal closes (`No goals to be solved`). Preserve the
  statement while repairing its proof; do not patch errors with assumptions.
