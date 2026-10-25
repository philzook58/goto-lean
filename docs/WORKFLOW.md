# Use your own C

Start with a sentence describing the intended behavior, admitted inputs and allowed
memory effects. Put properties in C assertions where practical.

## Generate

After the [one-time build](../README.md#build-once), from the repository root:

```sh
python3 tools/translate.py input.c --function process --out build/try
```

This retains raw/instrumented GOTO, a property inventory, and a checked `Model.lean`.
It creates a separate `Spec.lean` and Lake project, preserving your spec on reruns.
In an already-open VS Code file, restart the Lean file server after generation.
Failed generation leaves the previous model in place; check the command's result.

Use a dedicated output directory. For lasting work, put it outside ignored `build/`
and commit the spec, Lake configuration and toolchain; ignore regenerated models.
Repeat `--cc-arg=-I/path` or `--cc-arg=-DMACRO=value` for frontend arguments.

Read the generated checks before proving anything. The wrapper enables pointer,
bounds, signed-overflow, division and shift checks; it does not enable every CBMC
option. The inventory includes the whole translation unit, not just the selected
entry. See [coverage and limits](../COMPATIBILITY.md).

## Start with executions

Run the same boundary cases and seeded random inputs through native C and Lean.
Use native `-O0`, `-O2`, and ASan/UBSan where supported; compare relevant memory
as well as return values. Keep failing inputs and fuzz after smoke tests pass.
For signed maximum, include negative numbers and `INT_MIN`/`INT_MAX`.

For a translated `mymax`, the spec can start with:

```lean
import Model

#guard (v_mymax.eval 42 43 10 []).fst.getValue? == some 43
#guard (v_mymax.eval (.ofInt 32 (-3)) (.ofInt 32 (-2)) 10 []).fst.getValue?
  == some (.ofInt 32 (-2))
```

The starter has `ExampleRuns`, `BoundedExec` and `Specs` sections. Replace default
inputs, choices, memory and expected results with meaningful ones. A rejected
assumption, missing choice or exhausted run is not a successful example.

## Prove and recheck

Use the [proof guide](AGENT_GUIDE.md) for finite completion, loop invariants and
counterexamples, or follow the [runnable tutorials](TUTORIAL.md). The starter's
bounded `simp <;> bv_decide` sketch helps explore small bitvector goals; Lean
4.35.0's `bv_decide` may add native axioms rejected by our final audit.

The wrapper prints the command to check your spec. Audit named final claims with
the [skill checker](../.agents/skills/goto-lean/scripts/check_spec.py). Review the
statement as well as the proof: `Executes` describes one execution, `.wp` states
safety and partial correctness, and `finishes` adds completion under assumptions.
Memory premises need a caller or an explicit explanation.

Regenerate after C edits, rerun comparisons, and keep a deliberate failing case
that challenges the intended guarantee. For borrowed examples, record attribution
and changes beside the code; see [example guidelines](../AGENTS.md).
[Receipts](RECEIPTS.md) detect stale artifacts in the supported example runners;
[confidence limits](CONFIDENCE.md) explain what even a checked proof leaves open.
