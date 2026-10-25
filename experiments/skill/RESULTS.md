# goto-lean skill evaluation

[Round 2](ROUND2.md) adds 28 trials, compares compact/selected/full Lean guidance,
prunes instructions and tests a completion-shaped starter and checker.

Run on 2026-10-24 with `pi`, model
`openrouter/google/gemma-4-31b-it`, thinking level `low`, Lean 4.35.0.
These are exploratory trials of evolving instructions, not a controlled model
benchmark or a claim that the final skill reliably solves every task.

## What the evaluator received

Each fresh session received the skill, a draft of `docs/AGENT_GUIDE.md`, an
original local C task, the runtime implementation, the translator wrapper,
built tools and the runtime cache. It received **no existing example solutions,
controller proofs, previous trial answers or failure diagnoses**. The C tasks
were written locally for this experiment; none were imported from another
project. Expected behavior in the request was the specification, not a proof.

The runner copies only an explicit resource list. It excludes the repository's
`examples`, `tests`, other experiments, evaluation evidence and results. `pi`
ran with no saved session, context-file discovery, extensions, MCP, automatic
skills or prompt templates. The prompt restricted reading/writing to the trial
checkout, with Lean/Lake available for standard-library use. This was input
isolation and an agent instruction, not an OS-enforced security boundary.
Recorded reads and mutations show no access to solved examples. C and runtime
sources remained unchanged in all twelve trials.

The supplied templates teach general APIs; none gives a task's invariant,
expected-result expression, counterexample input or completed proof. In
particular, the generic Hoare-to-WP bridge proves no example program.

## Observed results

The controller independently compiled the final saved specs. Successful process
exit or an agent's written report was never sufficient evidence of correctness.

| Trial | Final artifact and result |
| --- | --- |
| `replay-v1` | Compiles; five signed boundary runs and zero-fuel rejection checked. Correct explanation of the overwritten declaration choice. Concrete executions only. |
| `bug-v1` | Fails compilation. Started with missing choices, then struggled with effect reduction and rewriting `eval` versus `evalLoop`. |
| `bug-v2` | Exact-site replay and safety refutation compile and pass independent axiom audits. The requested separate existential operational-witness theorem was omitted. |
| `prove-v1` | Fails compilation; left a `sorry` and an invalid local reference after struggling with the return state. |
| `prove-v2` | Fails compilation despite reporting success. Copied the inadequate starter sketch and used the unavailable `lemma` alias. |
| `prove-v3` | Compiles without an audit, but the independent audit rejects native `bv_decide` axioms. No accepted universal proof. |
| `prove-v4` | Effect unfolding works with the corrected starter. Its built-in audit rejects the remaining `bv_decide` axiom; the agent accurately reports this blocker. |
| `loop-v1` | Fails compilation: effect reduction and applying a Hoare triple directly to a WP goal. |
| `loop-v2` | Fails compilation: block obligations and the same Hoare/WP conversion. Reports unresolved obligations. |
| `loop-v3` | Reaches `vcgen` obligations but does not finish within 300 seconds. Final artifact fails compilation; it repeatedly simplifies without using invariant hypotheses. |
| `copy-vfinal` | Transfer task before the starter correction; times out after 240 seconds, with effects still folded. The label reflects when it was launched, not a final passing result. |
| `copy-v2` | After the starter correction, safety and input-equals-output theorem compile and pass an independent axiom audit. It exposes a `.wp` claim, not the requested separate completion theorem. |

All proofs were reviewed for their statement as well as compiler acceptance.
The last omission matters: a `.wp` theorem does not state termination even if
its proof internally constructs a bound using `finishes_run`. Similarly, the
bug trial's refutation does not export the requested witness interface.

Machine-readable times, tool counts and compile results are in
[`summary.json`](summary.json). The initial 18-tool-call instruction was not
enforced and was often exceeded; the current runner describes it as an aim.
Wall-clock limits are enforced. Parallel execution and changing instructions
make timing comparisons unsuitable for performance conclusions.

## Changes driven by the trials

- Added the repository skill and a guide separating concrete replay, universal
  checks, completion, loop safety and operational counterexamples.
- Explained declaration choices, small sufficient fuel and exact property-site
  replay before building failure certificates.
- Added the finite-effect unfolding recipe, a generic `vcgen` block template,
  and a checked Hoare-to-WP conversion using `.le_wp`.
- Distinguished `simp_all` on invariant hypotheses from goal-only `simp`, and
  explained removing tactics after a simplification closes the goal.
- Documented that this is a `Std` project and how to inspect actual library
  lemma signatures instead of guessing names or rewrite orientations.
- Documented native-reflection axioms from this pinned `bv_decide`, leaving the
  existing audit policy intact.
- Added `check_spec.py` to compile the current file and audit named public
  claims. It does not judge whether their statements meet the intended scope.
- Corrected the wrapper's generated documentation: the `Specs` sketch now
  unfolds effects, names the theorem, imports the audit and includes an audit
  command; bounded solver exploration is explicitly labeled. Existing specs
  remain preserved on regeneration.
- Made exported completion and operational-witness statements explicit after
  the final trials exposed scope omissions. Those last wording refinements
  have not been independently retested with the model.

The wrapper integration regression passes. The skill validator passes. Checker
tests accept a valid theorem and reject an added axiom, an unknown claim and an
invalid proof, while preserving the original spec and cleaning temporary files.
The generic Hoare-to-WP bridge was independently compiled and axiom-audited.

Remaining limitation: no trial produced an accepted general XOR proof or loop
proof. The skill now gives a better workflow and catches false success; these
results do not establish reliable autonomous proof completion. Memory contracts
and caller-premise construction were not evaluated.

## Reproduce without exposing solutions

Build the repository tools and runtime first. Configure `pi` with a writable
agent directory and access to the selected provider. Run from this repository:

```sh
python3 experiments/skill/evaluate.py --help
python3 experiments/skill/evaluate.py replay --out /tmp/goto-lean-replay
# Inspect the prepared inputs before making a model request.
python3 experiments/skill/evaluate.py prove \
  --out /tmp/goto-lean-prove-new --run --timeout 300
```

Use a fresh output directory for every trial. Set `PI_CODING_AGENT_DIR` if the
default pi configuration is read-only; credentials belong outside trial
directories. The initial tasks were `replay`, `prove`, `bug`, `loop` and `copy`;
`--help` lists the expanded current task set.
`--run` contacts the provider; preparing alone does not.

The runner saves the exact prompt, input hashes, trace, final artifacts and run
metadata. It independently compiles the final spec after the model exits.
Audit proof claims with the skill checker and review their types separately.
Future trials use current instructions, rather than recreating earlier drafts.

Compressed JSON records under [`evidence/`](evidence/) retain each trial's
prompt, skill/guide/wrapper snapshots, C, generated model, final spec, independent
compiler diagnostics, available audit results, read paths and shell commands.
They include solutions attempted by the evaluating agent and are **controller
evidence only**: the preparation script never copies them into a trial. Full
session traces remain under `/tmp/goto-lean-skill-eval/` for this local run;
their hashes are recorded in the retained evidence.

The subsequent [controlled comparison](CONTROLLED.md) verified one additional nondeterministic-choice completion proof, but provider credit interruptions prevented a comparison of guidance conditions.
