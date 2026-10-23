import GotoLean.Audit
import Increment
import Maximum
import Countdown
import Constrained

open GotoLean Std.WP Lean.Order
set_option experimental.vcgen true

namespace IncrementProof
private def invariant (x : BitVec 32) (f : v_increment.Frame) : Prop :=
  match f.1 with
  | .b0 => f.2.v_x = x
  | .b2 => f.2.result = some (x + 1)

private theorem block (x : BitVec 32) (f : v_increment.Frame) :
    ⦃invariant x f⦄ v_increment.step f ⦃Sum.elim (invariant x) (fun r => r = x + 1)⦄ := by
  rcases f with ⟨pc, s⟩
  cases pc <;> vcgen [v_increment.step]
  all_goals simp_all [invariant, Sum.elim]

theorem correct (x : BitVec 32) : ⦃True⦄ v_increment.run x ⦃fun r => r = x + 1⦄ := by
  constructor
  intro _
  apply (run_spec v_increment.step (v_increment.initial x) (invariant x)
    (fun r => r = x + 1) (fun f hi => by
      exact (block x f).le_wp hi)).le_wp
  simp [invariant, v_increment.initial]
end IncrementProof

namespace MaximumProof
private def selected (x y : BitVec 32) := if x.ult y then y else x
private def invariant (x y : BitVec 32) (f : v_maximum.Frame) : Prop :=
  match f.1 with
  | .b0 => f.2.v_x = x ∧ f.2.v_y = y
  | .b2 => f.2.result = some (selected x y)

private theorem block (x y : BitVec 32) (f : v_maximum.Frame) :
    ⦃invariant x y f⦄ v_maximum.step f
    ⦃Sum.elim (invariant x y) (fun r => r = selected x y)⦄ := by
  rcases f with ⟨pc, s⟩
  cases pc <;> vcgen [v_maximum.step]
  all_goals simp_all [invariant, selected, Sum.elim]

private theorem returns_selected (x y : BitVec 32) :
    (v_maximum.run x y).wp (fun r => r = selected x y) := by
  apply (run_spec v_maximum.step (v_maximum.initial x y) (invariant x y)
    (fun r => r = selected x y) (fun f hi => (block x y f).le_wp hi)).le_wp
  simp [invariant, v_maximum.initial]

theorem correct (x y : BitVec 32) :
    ⦃True⦄ v_maximum.run x y ⦃fun r => r.toNat = max x.toNat y.toNat⦄ := by
  constructor
  intro _
  apply (v_maximum.run x y).mono ?_ (returns_selected x y)
  intro r hr
  rw [hr]
  unfold selected
  split <;> simp_all [BitVec.ult, Nat.max_def] <;> omega
end MaximumProof

namespace CountdownProof
private def invariant (f : v_countdown.Frame) : Prop :=
  match f.1 with
  | .b0 | .b1 => True
  | .b3 => f.2.v_n = 0
  | .b6 => f.2.result = some 0

private theorem block (f : v_countdown.Frame) :
    ⦃invariant f⦄ v_countdown.step f
    ⦃Sum.elim invariant (fun r => r = 0)⦄ := by
  rcases f with ⟨pc, s⟩
  cases pc <;> vcgen [v_countdown.step]
  all_goals simp_all [invariant, Sum.elim]

theorem correct (n : BitVec 32) : ⦃True⦄ v_countdown.run n ⦃fun r => r = 0⦄ := by
  constructor
  intro _
  apply (run_spec v_countdown.step (v_countdown.initial n) invariant
    (fun r => r = 0) (fun f hi => (block f).le_wp hi)).le_wp
  trivial
end CountdownProof

namespace ConstrainedProof
private def invariant (f : v_constrained.Frame) : Prop :=
  match f.1 with
  | .b0 => True
  | .b10 => ∃ r, f.2.result = some r ∧ r.toNat < 10

private theorem block (f : v_constrained.Frame) :
    ⦃invariant f⦄ v_constrained.step f
    ⦃Sum.elim invariant (fun r => r.toNat < 10)⦄ := by
  rcases f with ⟨pc, s⟩
  cases pc <;> vcgen [v_constrained.step]
  all_goals simp_all [invariant, Sum.elim, BitVec.ult, BitVec.ule]
  all_goals omega

theorem correct : ⦃True⦄ v_constrained.run ⦃fun r => r.toNat < 10⦄ := by
  constructor
  intro _
  apply (run_spec v_constrained.step v_constrained.initial invariant
    (fun r => r.toNat < 10) (fun f hi => (block f).le_wp hi)).le_wp
  trivial
end ConstrainedProof

#check_axioms IncrementProof.correct
#check_axioms MaximumProof.correct
#check_axioms CountdownProof.correct
#check_axioms ConstrainedProof.correct
