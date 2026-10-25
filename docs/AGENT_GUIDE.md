# goto-lean proof guide

Use the repository [skill](../.agents/skills/goto-lean/SKILL.md) for the final
compiler/axiom check. [WORKFLOW.md](WORKFLOW.md) covers setup and specification
review; [REFERENCE.md](REFERENCE.md) describes supported semantics.
The checker's `--completion-claim` also requires a direct public `finishes`
statement; use `--claim` for other theorem forms. Bounds, postconditions and
extra hypotheses still need review.
For larger proofs, the checker accepts `--memory-mb 2048`; a resource-limit
failure leaves the claim unverified and is not a program counterexample.

## Translate and inspect

```sh
python3 tools/translate.py task.c --function entry --out build/task
lake -d build/task lean build/task/Spec.lean -- -j1 -M1024
```

The wrapper preserves `Spec.lean` on reruns. After C edits, regenerate and check
success: failed translation leaves the previous model in place. Inspect
`properties.txt` and `Model.lean`; the inventory covers the entire translation
unit, not just entry-reachable or proved properties. The wrapper inserts pointer,
bounds, signed-overflow, division-by-zero and undefined-shift checks. Raw-GOTO
translation does not insert those checks.

## Replay

Read `v_entry.eval`: argument order and memory/result shape vary. It returns
`(outcome, unusedChoices)`. `BitVec.ofInt 32 n` encodes signed inputs;
`toInt` decodes them. `slt` is signed comparison; `ult` is unsigned.

Each reached declaration consumes a choice, including overwritten locals.
Supply unsigned Nat bit patterns of the requested width in execution order.
Fuel counts entered basic blocks across calls. Check expected returns with
`#guard`, including memory effects where relevant:

| Outcome | Meaning |
| --- | --- |
| `returned value` | Completed execution |
| `assertionFailed site` | Failed program check |
| `assumptionRejected site` | Excluded path |
| `choiceError site` | Missing/out-of-range replay input |
| `exhausted block` | Insufficient replay fuel |

## Acyclic functions

For universal completion import `GotoLean.Termination` and state
`finishes v_entry.step fuel (v_entry.initial args) Q` for arbitrary inputs.
Choose a small bound covering every path, including the return block. Start by
reducing the effect layer:

```lean
simp [finishes, v_entry.step, v_entry.initial, Bind.bind,
  Action.wp_bind, choose, check, assume, Action.wp, Pure.pure, Sum.elim]
```

Replace the namespace and inspect residual goals. `Action.wp` makes choices
universal, checks conjunctions and assumptions implications. Thus even
`finishes` discards rejected assumptions: retain feasible returned examples.
`True` is a useful postcondition only when C assertions already express the
required result. `finishes_run` derives `.wp` from a completion theorem.
A symbolic `eval` equality with `[]` choices is not universal safety.
`simp made no progress` means no rewrite applied: inspect the current goal;
it does not mean the bound or generated program needs to change.
If reduction stops at a symbolic `if` inside `.wp`, use `split` and simplify
each branch with its hypothesis before treating the goal as pure arithmetic.

For residual comparisons, `simp [BitVec.ult, BitVec.ule, BitVec.slt] at *`
exposes Nat/Int arithmetic for `omega`. `BitVec.toNat_add` expresses modular
addition; prove its no-wrap bound rather than unfolding the BitVec representation.
Check unfamiliar lemma signatures with `#check` or search the installed Std
sources (`lean --print-prefix`). This project has no Mathlib tactics such as
`norm_num` or `aesop`.

## Loops

For unbounded partial correctness, define an invariant `I` on the generated
`Frame = PC × Locals`, including return PCs and the `result` field. Import
`Model` and `Std.Tactic.Do`, open `GotoLean Std.WP Lean.Order`, and enable
`set_option experimental.vcgen true`.

```lean
-- Define I and Q for the actual program; substitute its namespace.
theorem block (frame : v_entry.Frame) :
    ⦃I frame⦄ v_entry.step frame ⦃Sum.elim I Q⦄ := by
  rcases frame with ⟨pc, s⟩
  cases pc <;> vcgen [v_entry.step]
  all_goals simp_all [I, Q, Sum.elim]
```

Solve any remaining checks/arithmetic. `simp_all` uses the invariant hypotheses,
which goal-only `simp` leaves opaque. The API bridge to a WP goal is:

```lean
exact (run_spec step initial I Q preserves).le_wp starts
```

Here `starts : I initial` and
`preserves : ∀ s, I s → (step s).wp (Sum.elim I Q)`.
From a Hoare `block` theorem use
`fun s hi => (block s).le_wp hi` for `preserves`.
Applying the Hoare triple directly to `.wp` has the wrong type.

For termination use `finishes_of_rank` from `GotoLean.Termination`: every
continuing block must preserve the invariant and strictly decrease a Nat rank.
Include branch/return transitions, not just source loop iterations. A fixed
small fuel cannot certify an input-dependent loop for all inputs.

## Failures

Run the proposed witness first. Resolve `choiceError` before certifying a bug;
copy the exact failed site, including the intended property ID. A small replay
equality can be proved with `decide +kernel`; `#eval` alone is not a theorem.

`failure_refutes` in `GotoLean/Exec.lean` takes `step`, a frame description,
`initial`, `fuel`, `choices`, a proof that replay `isAssertionFailure = true`,
and `Q`. Its first projection gives an existential failed execution; its second
refutes `(run step initial).wp Q`. Export whichever witnesses were requested,
retaining the exact-site replay theorem because the existential erases that ID.

Its premise uses `evalLoop`. If a replay lemma about `v_entry.eval` will not
rewrite, use `change` to express the premise with the same generated wrapper,
then rewrite the outcome and reduce `Outcome.isAssertionFailure`. Input, fuel
and choices must agree.
