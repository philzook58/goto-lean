import GotoLean.Audit
import Nested
import Factorial
import CalleeBad
import CalleeDead
import CopyOverlap
import CopyBounds
import StringBad
import CallVoid
import LongBlock
import LongCalled

open GotoLean Std.WP Lean.Order
set_option experimental.vcgen true

#guard (v_nested.eval 9 100 [0, 0]).1 matches .choiceError _
#guard (v_factorial.eval 20 4 (List.replicate 128 0)).1 matches .exhausted _
#guard (v_callee_dead.eval 50 (List.replicate 20 0)).1 matches .assertionFailed _
#guard (v_copy_overlap.eval 20 (List.replicate 20 0)).1 matches .assertionFailed _
#guard (v_copy_bounds.eval 20 (List.replicate 20 0)).1 matches .assertionFailed _
#guard (v_string_bad.eval 20 (List.replicate 20 0)).1 matches .assertionFailed _
#guard (v_call_void.eval (Pointer.make 56 2 0) 20 []
  { objects := #[none, none, some #[0, 0, 0, 0]] }).1 ==
  .returned ((), { objects := #[none, none, some #[3, 0, 0, 0]] })

#guard v_long_block.eval 0 2 [7, 8] == (.returned 160, [8])
#guard (v_long_block.eval 0 1 [0]).1 matches .exhausted _
#guard (v_long_block.eval 0 2 []).1 matches .choiceError _
#guard (v_long_block.eval 4294967195 2 [0]).1 matches .assertionFailed _
#guard (v_long_block.eval 340 2 [0]).1 matches .assumptionRejected _
#guard (v_long_called.eval 4294967195 20 [0, 0]).1 matches .assertionFailed _
#guard (v_long_called.eval 340 20 [0, 0]).1 matches .assumptionRejected _

namespace CallProofs

/-- Recursion uses real stack frames; this certificate proves a concrete returning execution. -/
theorem factorial_execution : Executes v_factorial.step (v_factorial.initial 5)
    (.returned (120, {})) := by
  have h := evalLoop_exec v_factorial.step (fun f => reprStr f.1)
    100 (v_factorial.initial 5) (List.replicate 64 0)
  have evaluated : (v_factorial.eval 5 100 (List.replicate 64 0)).1 =
      .returned (120, {}) := by decide +kernel
  rw [show (evalLoop v_factorial.step (fun f => reprStr f.1)
    100 (v_factorial.initial 5) (List.replicate 64 0)).1 = _ from evaluated] at h
  exact h

theorem callee_counterexample : ¬ (v_callee_bad.run 7).wp (fun _ => True) :=
  (failure_refutes v_callee_bad.step (fun f => reprStr f.1) (v_callee_bad.initial 7)
    50 (List.replicate 20 0) (by decide +kernel) (fun _ => True)).2

theorem overlap_failure : (v_copy_overlap.eval 20 (List.replicate 20 0)).1.isAssertionFailure =
    true := by decide +kernel

theorem unterminated_failure : (v_string_bad.eval 20 (List.replicate 20 0)).1.isAssertionFailure =
    true := by decide +kernel

/-- The new library rule composes with vcgen and the ordinary object frame lemma. -/
theorem memcpy_frame (m : Memory) (dst src : BitVec 64) (size other : Nat)
    (source : m.valid 56 src size = true) (dest : m.valid 56 dst size = true)
    (disjoint : Memory.disjoint 56 dst src size = true)
    (separate : Pointer.object 56 dst ≠ other) :
    ⦃True⦄ m.memcpy "copy" 56 dst src size
      ⦃fun (_, m') => m'.bytes other = m.bytes other⦄ := by
  vcgen
  exact ⟨source, dest, disjoint, Memory.bytes_put_other m _ other _ separate⟩

#check_axioms factorial_execution
#check_axioms callee_counterexample
#check_axioms overlap_failure
#check_axioms unterminated_failure
#check_axioms memcpy_frame

end CallProofs
