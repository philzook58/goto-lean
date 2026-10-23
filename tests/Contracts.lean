import GotoLean.Audit
import Factorial
import GotoLean.Contracts

/-! A universal recursive proof using local contracts, without a user-written stack invariant. -/
namespace ContractTests
open GotoLean Std.WP Lean.Order

def factorial : Nat → BitVec 32
  | 0 => 1
  | n + 1 => BitVec.ofNat 32 (n + 1) * factorial n

private theorem factorial_step (n : BitVec 32) (h : n ≠ 0) :
    factorial n.toNat = n * factorial (n - 1).toNat := by
  have hn : 0 < n.toNat := by
    have : n.toNat ≠ 0 := by
      intro hz
      apply h
      apply BitVec.eq_of_toNat_eq
      simpa using hz
    omega
  have hs : (n - 1).toNat + 1 = n.toNat := by
    change ((2 ^ 32 - 1 + n.toNat) % 2 ^ 32) + 1 = n.toNat
    have := n.isLt
    omega
  rw [← hs, factorial, hs, BitVec.ofNat_toNat]
  simp

private def invariant (frame : v_factorial.Activation) (Q : v_factorial.Value → Prop) : Prop :=
  match frame with
  | .v_factorial (pc, s) =>
    match pc with
    | .b0 => Q (.v_factorial (factorial s.v_n.toNat, s.memory))
    | .b1 => s.v_n = 0 ∧ Q (.v_factorial (1, s.memory))
    | .b3 => s.v_n ≠ 0 ∧ Q (.v_factorial (factorial s.v_n.toNat, s.memory))
    | .b6 => Q (.v_factorial (s.v_n * s.v_return_value_factorial, s.memory))
    | .b9 => ∃ r, s.result = some r ∧ Q (.v_factorial (r, s.memory))

private theorem blocks (frame : v_factorial.Activation) (Q : v_factorial.Value → Prop)
    (hi : invariant frame Q) : (v_factorial.body frame).wp (Transfer.wp · invariant Q) := by
  rcases frame with ⟨pc, s⟩
  cases pc with
  | b0 =>
    simp only [v_factorial.body]
    split <;> simp_all [Action.wp_pure, Transfer.wp, invariant, factorial]
  | b1 =>
    obtain ⟨hn, hq⟩ := hi
    exact ⟨1, rfl, hq⟩
  | b3 =>
    obtain ⟨hn, hq⟩ := hi
    simp only [v_factorial.body, Bind.bind, Action.wp_bind, choose, Action.wp]
    intro choice
    refine ⟨(· = .v_factorial (factorial (s.v_n - 1).toNat, s.memory)), ?_, ?_⟩
    · simp [invariant, v_factorial.Functions.v_factorial.initial]
    · intro value hv
      subst value
      change Q (.v_factorial (s.v_n * factorial (s.v_n - 1).toNat, s.memory))
      rw [← factorial_step s.v_n hn]
      exact hq
  | b6 => exact ⟨s.v_n * s.v_return_value_factorial, rfl, hi⟩
  | b9 =>
    obtain ⟨r, hr, hq⟩ := hi
    simpa [v_factorial.body, hr, Transfer.wp, Action.wp_pure] using hq

/-- The original generated recursive function returns the mathematical factorial modulo 2^32.
This proves safety and partial correctness for every input and every finite prefix. -/
theorem factorial_correct (n : BitVec 32) (m : Memory) :
    (v_factorial.run n m).wp (fun (r, m') ↦ r = factorial n.toNat ∧ m' = m) := by
  apply (calls_spec v_factorial.body v_factorial.finish invariant
    (.v_factorial (v_factorial.Functions.v_factorial.initial n m))
    (· = .v_factorial (factorial n.toNat, m)) _ blocks ?_).le_wp
  · simp [invariant, v_factorial.Functions.v_factorial.initial]
  · intro value hv
    subst value
    exact ⟨rfl, rfl⟩

#check_axioms factorial_correct
#check_axioms calls_spec

end ContractTests
