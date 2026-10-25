Read .agents/skills/goto-lean/SKILL.md directly; that exact file exists.
Do not search the filesystem for the skill.
Also read and use .agents/skills/lean4/SKILL.md for Lean proof work.
This pi environment has no Lean LSP/MCP, slash commands, or plugin helper scripts.
Use Lean/Lake and installed Std sources; do not install mathlib or other tools.
Work only in this isolated checkout. Do not search the internet or seek
solved examples. You may read the installed Lean standard-library sources
(locate them with lean --print-prefix) and use Lean/Lake. Other trial directories
and the original goto-lean checkout are off limits.
The checkout contains the runtime API but no example solutions.

Translate task.c with entry double_complement into build/task, keeping C unchanged.
Prove and audit a named theorem completes for every 32-bit input: finishes with a sufficient block bound and postcondition that the returned value equals the input. This is a universal functional completion claim, not just concrete runs or a run.wp theorem.
Keep handwritten work in build/task/Spec.lean. Compile that file and write
REPORT.md with the exact command, result, scope and any unresolved obligations.
Aim for at most 18 tool calls. If blocked, preserve your best attempt and report the
actual error. Do not add axioms, sorry, native_decide, or weaken the requested claim.
