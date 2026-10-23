import GotoLean.Audit
import LockFixed
import Guarded
import RangeFixed

open GotoLean Std.WP Lean.Order
set_option experimental.vcgen true

namespace LockProof
-- The two important facts are that the loop head is unlocked and the join agrees on ownership.
private def invariant (frame : v_lock_fixed.Frame) : Prop :=
  let s := frame.2
  match frame.1 with
  | .b0 => True
  | .b4 | .b5 | .b8 | .b13 | .b19 => s.v_got_lock = 0 ∧ s.v_held = 0
  | .b14 => (s.v_got_lock = 0 ∧ s.v_held = 0) ∨ (s.v_got_lock = 1 ∧ s.v_held = 1)
  | .b16 => s.v_got_lock = 1 ∧ s.v_held = 1
  | .b22 => s.v_got_lock = 0
  | .b27 => s.result = some 0

private theorem block (frame : v_lock_fixed.Frame) :
    ⦃invariant frame⦄ v_lock_fixed.step frame
    ⦃Sum.elim invariant (fun r => r = 0)⦄ := by
  rcases frame with ⟨pc, s⟩
  cases pc <;> vcgen [v_lock_fixed.step]
  all_goals simp_all [invariant, Sum.elim]

/-- Safety for every 32-bit iteration count and every sequence of lock-acquisition choices. -/
theorem correct (times : BitVec 32) :
    ⦃True⦄ v_lock_fixed.run times ⦃fun r => r = 0⦄ := by
  constructor
  intro _
  exact (run_spec v_lock_fixed.step (v_lock_fixed.initial times) invariant (fun r => r = 0)
    (fun s hi => (block s).le_wp hi)).le_wp trivial
end LockProof

#check_axioms LockProof.correct

namespace GuardedProof
private def invariant (frame : v_guarded.Frame) : Prop :=
  match frame.1 with
  | .b0 | .b2 => True
  | .b1 => frame.2.v_x.sle 42 = true
  | .b5 => frame.2.result = some 0

private theorem block (frame : v_guarded.Frame) :
    ⦃invariant frame⦄ v_guarded.step frame ⦃Sum.elim invariant (fun r => r = 0)⦄ := by
  rcases frame with ⟨pc, s⟩
  cases pc <;> vcgen [v_guarded.step]
  all_goals simp_all [invariant, Sum.elim]
  all_goals intro h; simp_all [BitVec.sle]

theorem correct (x : BitVec 32) : ⦃True⦄ v_guarded.run x ⦃fun r => r = 0⦄ := by
  constructor
  intro _
  exact (run_spec v_guarded.step (v_guarded.initial x) invariant (fun r => r = 0)
    (fun s hi => (block s).le_wp hi)).le_wp trivial
end GuardedProof

namespace RangeProof
private def invariant (frame : v_range_fixed.Frame) : Prop :=
  match frame.1 with
  | .b0 => True
  | .b4 => ∃ r, frame.2.result = some r ∧ r.toNat ≤ 100

private theorem block (frame : v_range_fixed.Frame) :
    ⦃invariant frame⦄ v_range_fixed.step frame ⦃Sum.elim invariant (fun r => r.toNat ≤ 100)⦄ := by
  rcases frame with ⟨pc, s⟩
  cases pc <;> vcgen [v_range_fixed.step]
  all_goals simp_all [invariant, Sum.elim, BitVec.ule]

theorem correct (x : BitVec 32) : ⦃True⦄ v_range_fixed.run x ⦃fun r => r.toNat ≤ 100⦄ := by
  constructor
  intro _
  apply (run_spec v_range_fixed.step (v_range_fixed.initial x) invariant (fun r => r.toNat ≤ 100)
    (fun s hi => (block s).le_wp hi)).le_wp
  trivial
end RangeProof

#check_axioms GuardedProof.correct
#check_axioms RangeProof.correct
