import GotoLean.Audit
import Maximum
import Countdown
import Irreducible

/-! Handwritten encoding experiments on the existing C fixtures, not another translator.
All effectful variants reuse GotoLean.Action and the existing proof/execution runners. -/
open GotoLean Std.WP Lean.Order
set_option experimental.vcgen true
set_option experimental.intrinsic true

namespace Direct
-- An acyclic function can simply be an Action returning a native Lean expression.
def maximum (x y : BitVec 32) : Action (BitVec 32) :=
  pure (if x.ult y then y else x)

theorem maximum_correct (x y : BitVec 32) :
    ⦃True⦄ maximum x y ⦃fun r => r.toNat = max x.toNat y.toNat⦄ := by
  vcgen [maximum]
  all_goals simp_all [BitVec.ult, Nat.max_def]
  all_goals split <;> simp_all <;> omega

-- Equivalence of arbitrary postconditions, not merely one functional specification.
theorem maximum_equiv (x y : BitVec 32) (Q : BitVec 32 → Prop) :
    (v_maximum.run x y).wp Q ↔ (maximum x y).wp Q := by
  constructor
  · intro h
    have h₂ := h 2
    by_cases hxy : x.ult y = true <;>
      simpa [v_maximum.step, v_maximum.initial, safe, maximum, hxy] using h₂
  · intro h fuel
    cases fuel with
    | zero => trivial
    | succ fuel =>
      cases fuel with
      | zero => trivial
      | succ fuel =>
        by_cases hxy : x.ult y = true <;>
          simpa [v_maximum.step, v_maximum.initial, safe, maximum, hxy] using h
end Direct

namespace Blocks
-- Local values travel with the block that needs them. No global record or Option return slot.
inductive State where
  | test (n : BitVec 32)
  | decrement (n : BitVec 32)
  | finish (result : BitVec 32)
  deriving Repr

def test (n : BitVec 32) : Action (Next State (BitVec 32)) :=
  pure (if n == 0 then .inl (.finish n) else .inl (.decrement n))
def decrement (n : BitVec 32) : Action (Next State (BitVec 32)) :=
  pure (.inl (.test (n - 1)))
def finish (r : BitVec 32) : Action (Next State (BitVec 32)) := pure (.inr r)

def step : Step State (BitVec 32)
  | .test n => test n
  | .decrement n => decrement n
  | .finish r => finish r

def program (n : BitVec 32) := run step (.test n)

private def invariant : State → Prop
  | .test _ | .decrement _ => True
  | .finish r => r = 0

private theorem block (s : State) :
    ⦃invariant s⦄ step s ⦃Sum.elim invariant (fun r => r = 0)⦄ := by
  cases s <;> vcgen [step, test, decrement, finish]
  all_goals simp_all [invariant, Sum.elim]
  all_goals split <;> simp_all

theorem correct (n : BitVec 32) : ⦃True⦄ program n ⦃fun r => r = 0⦄ := by
  constructor
  intro _
  exact (run_spec step (.test n) invariant (fun r => r = 0)
    (fun s hi => (block s).le_wp hi)).le_wp trivial
end Blocks

namespace Loop
-- Collapsing the loop guard/body and return tail removes the PC completely here.
def step (n : BitVec 32) : Action (Next (BitVec 32) (BitVec 32)) :=
  pure (if n == 0 then .inr n else .inl (n - 1))
def program (n : BitVec 32) := run step n

theorem correct (n : BitVec 32) : ⦃True⦄ program n ⦃fun r => r = 0⦄ := by
  constructor
  intro _
  apply (run_spec step n (fun _ => True) (fun r => r = 0) ?_).le_wp trivial
  intro s _
  have block : ⦃True⦄ step s ⦃Sum.elim (fun _ => True) (fun r => r = 0)⦄ := by
    vcgen [step]
    all_goals simp_all [Sum.elim]
    all_goals split <;> simp_all
  exact block.le_wp trivial
end Loop

namespace Structured
-- A pure Lean while loop has the nicest surface syntax, but needs a termination proof.
def countdown (input : BitVec 32) : Id (BitVec 32) := do
  let mut n := input
  while n != 0
    invariant exit => exit = true → n = 0
    decreasing n.toNat
  do
    n := n - 1
  return n

theorem correct (n : BitVec 32) : countdown n = 0 := by
  apply Id.of_run_eq_wp (prog := countdown n) rfl (fun r => r = 0)
  simp only [countdown]
  vcgen
  all_goals simp_all [BitVec.toNat_eq]
  all_goals omega
end Structured

namespace IrreducibleBlocks
-- This graph has two entrances to a cycle, so a single natural while loop is insufficient.
inductive State where
  | a (x n : BitVec 32)
  | b (x n : BitVec 32)
  deriving Repr

def a (x n : BitVec 32) : Action (Next State (BitVec 32)) :=
  pure (if n == 0 then .inr x else .inl (.b (x + 3) (n - 1)))
def b (x n : BitVec 32) : Action (Next State (BitVec 32)) :=
  pure (if n == 0 then .inr x else .inl (.a (x ^^^ 7) (n - 1)))
def step : Step State (BitVec 32)
  | .a x n => a x n
  | .b x n => b x n

def initial (x n : BitVec 32) : State :=
  if x &&& 1 != 0 then .b x n else .a x n
end IrreducibleBlocks

-- Concrete comparisons use ample fuel, not equal fuel: collapsing blocks changes its unit.
def main : IO Unit := do
  let values : List (BitVec 32) := [0, 1, 7, 2147483647, 2147483648, 4294967295]
  for x in values do
    for y in values do
      unless (Direct.maximum x y).eval [] == v_maximum.eval x y 10 do
        throw (IO.userError "direct maximum differs")
  for n in [:65] do
    let input := BitVec.ofNat 32 n
    let expected := v_countdown.eval input 1000
    unless evalLoop Blocks.step reprStr 1000 (.test input) [] == expected do
      throw (IO.userError "block-argument countdown differs")
    unless evalLoop Loop.step reprStr 1000 input [] == expected do
      throw (IO.userError "collapsed-loop countdown differs")
    unless expected.1 == .returned (Structured.countdown input) do
      throw (IO.userError "structured countdown differs")
    for x in values do
      unless evalLoop IrreducibleBlocks.step reprStr 1000
          (IrreducibleBlocks.initial x input) [] == v_irreducible.eval x input 1000 do
        throw (IO.userError "irreducible blocks differ")
  IO.println "PASS encoding experiments: 621 comparisons with generated GOTO programs"

#check_axioms Direct.maximum_equiv
#check_axioms Blocks.correct
#check_axioms Loop.correct
#check_axioms Structured.correct
