import GotoLean.Audit
import GotoLean.Paths

namespace PathTests
open GotoLean

private def failing : Step Nat Unit := fun s ↦
  if s = 0 then .done (.inl 1) else .check "later failure" false (.done (.inr ()))

/-- A checkpoint immediately before a failed check cannot hide that check. -/
theorem failure_after_checkpoint :
    ¬ finishes (path failing (· == 1) 1) 2 0 (fun _ ↦ True) := by
  simp [finishes, path, failing, Bind.bind, Action.wp_bind, Action.wp_pure, Action.wp]

private def looping : Step Unit Unit := fun _ ↦ .done (.inl ())

/-- Omitting a checkpoint from a cycle exhausts the path budget and fails the proof. -/
theorem missing_checkpoint :
    ¬ (path looping (fun _ ↦ false) 3 ()).wp (fun _ ↦ True) := by
  simp [path, looping, Bind.bind, Action.wp]

/-- Even a checkpoint at every step cannot establish bounded completion of a cycle. -/
theorem looping_checkpoint :
    ¬ finishes (path looping (fun _ ↦ true) 1) 3 () (fun _ ↦ True) := by
  simp [finishes, path, looping, Bind.bind, Action.wp_pure]

#check_axioms failure_after_checkpoint
#check_axioms missing_checkpoint
#check_axioms looping_checkpoint
end PathTests
