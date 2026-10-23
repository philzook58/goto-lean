import Checked.Caller
import Checked.CallerBug
import GotoLean.Termination

/-! Read with `caller.c`: the caller creates its own array and has no input preconditions. -/
namespace ArrayExamples.CallerSpec
open GotoLean

/-- For every 32-bit value, the caller passes all checks, returns that value, and releases
its local array. The initial modeled memory is empty; no memory facts are assumed. -/
def fill_local : Prop :=
  ∀ value : BitVec 32, ∃ blocks,
    finishes v_fill_local.step blocks (v_fill_local.initial value)
      (fun (result, after) ↦ result = value ∧ after.bytes 2 = none)

/-- Filling only three elements can reach the caller's named endpoint assertion. -/
def underfill : Prop :=
  ∃ site, site.toSlice.endsWith "; property fill_local_bug.assertion.1; underfilled array" = true ∧
    Executes v_fill_local_bug.step (v_fill_local_bug.initial 1) (.assertionFailed site)

end ArrayExamples.CallerSpec
