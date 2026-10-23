import GotoLean.Audit
import Increment
import Maximum

/-! Checked proof views of the unchanged generated programs.
The summaries quantify over every postcondition; they are not additional execution models. -/
namespace ProofViews
open GotoLean

theorem increment_wp (x : BitVec 32) (Q : BitVec 32 → Prop) :
    (v_increment.run x).wp Q ↔ Q (x + 1) := by
  constructor
  · intro h
    simpa [safe, v_increment.step, v_increment.initial, Action.wp] using h 2
  · intro h fuel
    match fuel with
    | 0 => trivial
    | 1 => trivial
    | _ + 2 => simpa [safe, v_increment.step, v_increment.initial, Action.wp] using h

theorem maximum_wp (x y : BitVec 32) (Q : BitVec 32 → Prop) :
    (v_maximum.run x y).wp Q ↔ Q (if x.ult y then y else x) := by
  constructor
  · intro h
    by_cases hxy : x.ult y = true <;>
      simpa [safe, v_maximum.step, v_maximum.initial, Action.wp, hxy] using h 2
  · intro h fuel
    match fuel with
    | 0 => trivial
    | 1 => trivial
    | _ + 2 =>
      by_cases hxy : x.ult y = true <;>
        simpa [safe, v_maximum.step, v_maximum.initial, Action.wp, hxy] using h

-- These client proofs do not mention PCs, record fields, return slots or fuel.
theorem increment_correct (x : BitVec 32) :
    (v_increment.run x).wp (fun r => r = x + 1) := by
  rw [increment_wp]

theorem maximum_is_input (x y : BitVec 32) :
    (v_maximum.run x y).wp (fun r => r = x ∨ r = y) := by
  rw [maximum_wp]
  split <;> simp

theorem maximum_correct (x y : BitVec 32) :
    (v_maximum.run x y).wp (fun r => r.toNat = max x.toNat y.toNat) := by
  rw [maximum_wp]
  split <;> simp_all [BitVec.ult, Nat.max_def] <;> omega

#check_axioms increment_wp
#check_axioms maximum_wp
#check_axioms increment_correct
#check_axioms maximum_correct

end ProofViews
