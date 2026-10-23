import Uninitialized
import Abs64
import AfterAssume
import Std.Tactic.BVDecide

open GotoLean

-- These claims are false. Check that bv_decide finds the expected counterexamples.
/--
error: The prover found a counterexample, consider the following assignment:
x = 12345#32
-/
#guard_msgs in
example : safe v_uninitialized.step 1 v_uninitialized.initial (fun _ => True) := by
  simp only [safe, v_uninitialized.step, v_uninitialized.initial, check, choose,
    Bind.bind, Action.bind, Action.wp]
  intro x
  simp only [Action.wp_pure, Sum.elim, and_true]
  bv_decide

/--
error: The prover found a counterexample, consider the following assignment:
x = 9223372036854775808#64
-/
#guard_msgs in
example (x : BitVec 64) : safe v_abs64.step 1 (v_abs64.initial x) (fun _ => True) := by
  simp [safe, v_abs64.step, v_abs64.initial, check, choose, Bind.bind, Action.bind, Action.wp]
  bv_decide

/--
error: The prover found a counterexample, consider the following assignment:
x = 100#32
-/
#guard_msgs in
example (x : BitVec 32) : safe v_after_assume.step 1 (v_after_assume.initial x)
    (fun _ => True) := by
  simp [safe, v_after_assume.step, v_after_assume.initial, check, assume,
    Bind.bind, Action.bind, Action.wp]
  bv_decide
