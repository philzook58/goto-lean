# Controlled Gemma guidance comparison

2026-10-24. **One new requested proof verified; the guidance comparison is inconclusive because OpenRouter credits interrupted it.** The user explicitly approved sending the isolated source, documentation and tool outputs to Gemma through OpenRouter.

## Results

| Guidance | Verified requested proof | Provider interrupted after generation | Provider rejected before generation |
| --- | ---: | ---: | ---: |
| Compact goto-lean skill | 1 | 4 | 4 |
| Compact skill + selected Lean notes | 0 | 1 | 8 |

These are exposure categories, **not comparative success rates**. The provider errors made exposure unequal. Five sessions generated work before a credit interruption; twelve produced no model work. Do not count those twelve as Lean proof failures or infer an advantage for either guidance condition.

The accepted compact-skill run was `choice-compact-1`. Gemma exported `completes`, asserting universal `finishes` within two blocks with postcondition `r.toNat < 16`, under the unchanged source assumption. The agent's process reached its 180-second limit after writing the proof and report; the saved proof independently passed the compiler, the exact requested-statement adapter, and the axiom audit. C, generated model, runtime, guidance and translator stayed unchanged. This is a completed proof artifact, despite the process timeout. The controlled choice prompt requested completion only, so this result does not also certify a replay witness.

## Frozen design

Three tasks: double complement, nondeterministic choice, conditional unsigned cap. Three fresh attempts per condition, 18 scheduled sessions. Pi used `openrouter/google/gemma-4-31b-it`, low thinking, a 180-second model budget, and at most three simultaneous sessions. Trial order was shuffled with seed 20261024. All workspaces were prepared before calls; no feedback or guidance changes occurred during the restarted study. Solutions and prior attempts were excluded.

The intervention was the compact goto-lean skill versus the same skill plus [194 words of selected Lean notes](controlled/selected-lean.md). Each condition had one combined preloaded system-guidance file. The selected condition additionally had the notes file and an instruction to read it. Task C, generated model, runtime, translator and guide were identical within each task.

A pass required a public `completes` theorem directly stating `finishes`, matching the requested inputs and result through a controller-only Lean adapter, compiling, and passing the axiom audit. The adapter allowed any sufficient fuel bound and was added after the agent exited. Protected input changes invalidated a pass. Controller-only validation accepted a valid proof and rejected both a weakened postcondition and an extra assumption. No validation solutions were provided to Gemma.

## What the traces show

Five of the six sessions that generated work did not read `AGENT_GUIDE.md`, through either the read tool or a shell command. The successful choice session did read it, then used its effect-reduction recipe and unsigned-comparison reduction. This is an observation, not evidence that reading the guide caused success.

The three interrupted branch attempts repeatedly unfolded or simplified without resolving the remaining goal. One left a `sorry`, correctly rejected by the audit. The selected-notes branch attempt reached residual `BitVec.ule` obligations but stopped before discharging them; grading also encountered the configured kernel memory limit. The selected notes did not ensure that Gemma read the existing branch/comparison guidance.

After all model runs exited, controller-only checks produced compiling, axiom-audited proofs of choice and branch using techniques already in the guide. These are task/guide sanity checks, not Gemma successes, and were never passed to the evaluated agents.

**Skill decision:** keep the compact skill and guide unchanged. This interrupted sample does not justify adding a default Lean-skill dependency or deleting existing instructions. The next useful comparison is whether preloading the relevant guide section helps more than linking it; run fresh tasks with sufficient provider credits before making that change the default.

## Infrastructure and retained evidence

The initial launch returned HTTP 402 errors for all 18 sessions before any generation because the catalog default requested up to 233,602 output tokens. All workspaces were recreated, and a common 8,192-token maximum per response was applied before restarting. These initial failures are archived separately and excluded from the table. The restarted sessions then encountered OpenRouter credit/reservation errors; a read-only account check confirmed that the credit balance was exhausted. Further model trials require replenished credits. No billing changes were made.

[Protocol](controlled/protocol.json), [assessments](controlled/summary.json), six task/condition prompts, the [common model override](controlled/pi-models.json), and compressed [evidence](controlled/evidence) are retained. Evidence includes original traces, final specs/models/reports, grading logs, hashes, and frozen common sources/guidance/harness. Temporary authentication was removed after the runs. Installed Lean Std sources were permitted; no solved examples were supplied. The model could read only its isolated checkout and installed standard library under the task instructions; these are behavioral isolation rules, not an operating-system read sandbox.
