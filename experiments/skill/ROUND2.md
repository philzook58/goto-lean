# Round 2: pruning and Lean-skill comparisons

2026-10-24. **28 additional pi/Gemma-4-31B trials**, following the initial twelve.
Most used low thinking and 180 seconds; three used high thinking, including
one 240-second loop trial. These evolving, single-run experiments are not a
statistical benchmark.

## Pruning

| Model-facing instructions | Before | After |
| --- | ---: | ---: |
| goto-lean skill | 490 words | 299 words |
| Agent guide | 1,832 words | 773 words |
| Combined | 2,322 words | 1,072 words |

The combined instructions are **54% shorter**. Removed repeated warnings,
generic troubleshooting, duplicated API explanations and setup prose covered
elsewhere. Retained exact APIs, reduction rules, the invariant bridge, replay
semantics and the checking command.

## General Lean skill comparison

Compared compact goto-lean guidance alone, with a 194-word selection of Lean
techniques, and with the installed lean4 4.11.4 skill and references. The full
entry point alone is 3,852 words.

| Matched task | Compact | Selected notes | Full Lean skill |
| --- | --- | --- | --- |
| Addition under a source assumption | Failed | Failed | Failed |
| Conditional unsigned cap | Failed | Failed | Failed |
| Unbounded countdown safety | Failed | Failed | Failed |
| Cap with preloaded guidance and revised starter | Failed | Failed | Failed |

On double complement, compact and full-skill sessions both produced compiling,
axiom-audited **WP** claims, missing the requested public completion statement.
Neither completed that task.

Adding the full skill showed **no verified improvement in these tests**. It
remains optional, not a goto-lean dependency. This conclusion concerns pi with
shell tools and Std: no Lean LSP/MCP, slash commands, helper runtime or Mathlib.
It does not measure the complete Lean plugin in its supported environment.

Selected notes paraphrased the installed skill's search-first, incremental
validation, goal-structure and error-diagnosis guidance, from `SKILL.md`,
`references/tactic-patterns.md` and `references/compilation-errors.md`.
The installed 4.11.4 entry point declares MIT licensing. Its hash is recorded;
full upstream text is not vendored. Selected notes remain experimental input,
not another default skill.

## Findings from Gemma's returned reasoning

The provider returned reasoning blocks. Reviewing them with tool calls and
compiler errors revealed recurring mistakes:

- Guessing that `finishes` takes replay choices.
- Counting C declarations to introduce binders after simplification had removed
  overwritten values.
- Unfolding more blocks after the goal was already arithmetic.
- Repeating `simp` without examining the residual goal.
- Attempting termination before completing requested safety.
- Reporting a public `.wp` theorem as completion.

The retained guidance now gives exact argument order, uses `trace_state`,
explains why `simp only [step]` bypasses the starter's reduction rules, and
requires the requested public theorem shape. Three repair trials received
Gemma's own failed artifact plus procedural feedback; all still failed. These
were separately marked repair trials, not cold evaluations.

## Accepted result and scaffolding

The wrapper now provides local block/effect reduction rules in `Specs` and a
**completion-shaped** theorem template. Its old WP-shaped template repeatedly
anchored the agent to a weaker public claim despite explicit completion requests.

The compact-only session with the new template produced this public claim:

```lean
theorem completes (v_x : BitVec 32) :
    finishes v_double_complement.step 2 (v_double_complement.initial v_x)
      (fun result ↦ result = v_x)
```

The controller independently compiled and axiom-audited the saved proof. This
is the **one fully accepted requested proof among the 28 trials**. There were
no added hypotheses or C assumptions. The handwritten functional contract is
the claim; this example has no C assertion inventory to prove.

The checker now offers `--completion-claim`: besides auditing axioms, it checks
that the public result type is directly `finishes` after universal binders.
It rejects the earlier WP artifacts. Bounds, postconditions and hypotheses still
need review; existential completion formulations can use ordinary `--claim`.

Remaining failures include arithmetic, conditional caps, choices and unbounded
loops. The choice task reached a feasible returned replay but failed on binder
handling and syntax. Fixed-loop attempts included discovery stalls and kernel
memory failures. A controller-only simplification probe reproduced the latter
at both 1,024 and 2,048 MB. That indicates a proof-reduction/scaling issue to
investigate, not proof that the theorem is difficult or impossible. The probe
was never supplied to an evaluating agent.

## Evaluation fixes and evidence

Two sessions searched the filesystem for `SKILL.md` instead of reading the given
path. Later trials preloaded skill bodies into pi's system context. Broad scans
were recorded; no subsequent content reads outside the trial and permitted Std
sources were found. The first arithmetic group also inherited unrelated old
test sources from `.lake`; these were not task solutions but added search noise.
The runner now copies only `.lake/build` runtime artifacts.

Existing examples, other experiments, controller work and previous successful
solutions are excluded. Repair trials seed only a failed agent artifact. All
C and runtime sources remained unchanged.

[`round2-summary.json`](round2-summary.json) records all outcomes, budgets, tool
counts and reasoning counts. Compressed JSON under
[`evidence/round2/`](evidence/round2/) retains prompts, guidance/wrapper snapshots,
final artifacts, diagnostics, reads/commands and returned Gemma reasoning in
`gemma_reasoning`. Full traces remain in `/tmp/goto-lean-round2/`; their hashes
are recorded. Evidence is excluded from prepared workspaces.

Validation passed: wrapper integration regression, skill validation, Python
syntax checks, and checker tests accepting genuine completion and ordinary WP
claims while rejecting WP requested as completion, an added axiom and an unknown
theorem. Tests also checked spec preservation and temporary-file cleanup.

Reproduce from the repository root with a fresh output directory:

```sh
python3 experiments/skill/evaluate.py choice \
  --out /tmp/goto-lean-choice-new --run --preload-guidance --timeout 180
```

`--lean-skill DIR` adds a skill; `--skill-source` and `--guide-source` choose
comparison inputs; `--thinking high` changes effort; `--attempt-source FILE`
marks a repair trial. Keep pi credentials outside trials. Retained snapshots
identify the exact evolving instructions each run saw.
