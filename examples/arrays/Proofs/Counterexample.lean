import Generated.Bug
import Proofs.Array

namespace ArrayExamples.Counterexample
open GotoLean

def memory : Memory :=
  { objects := #[none, none, some #[1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0]] }
def pointer : BitVec 64 := Pointer.make 56 2 0

/-- The single `<` to `≤` mutation returns the wrong index on three equal keys. -/
theorem replay :
    (v_lower_bound_bug.eval pointer 3 1 40 [0, 0, 0, 0] memory).1 =
      .returned (3, memory) := by decide +kernel

/-- The replay is an operational execution of the generated blocks. -/
theorem executed : Executes v_lower_bound_bug.step
    (v_lower_bound_bug.initial pointer 3 1 memory) (.returned (3, memory)) := by
  have h := evalLoop_exec v_lower_bound_bug.step (fun f ↦ reprStr f.1) 40
    (v_lower_bound_bug.initial pointer 3 1 memory) [0, 0, 0, 0]
  change (v_lower_bound_bug.eval pointer 3 1 40 [0, 0, 0, 0] memory).1.Corresponds _ at h
  rw [replay] at h
  exact h

/-- The observed execution refutes the original partition contract for the mutant. -/
theorem refutes_contract :
    ¬ (v_lower_bound_bug.run pointer 3 1 memory).wp
      (fun (r, m) ↦ Partition (fun _ ↦ 1) 3 1 r.toNat r.toNat ∧ m = memory) := by
  intro claim
  have h := run_eval_sound v_lower_bound_bug.step (fun f ↦ reprStr f.1)
    (v_lower_bound_bug.initial pointer 3 1 memory) _ claim 40 [0, 0, 0, 0]
  change (v_lower_bound_bug.eval pointer 3 1 40 [0, 0, 0, 0] memory).1.Satisfies _ at h
  rw [replay] at h
  have impossible := h.1.2.2.1 0 (by decide)
  simp at impossible

end ArrayExamples.Counterexample
