import Generated.Abs
import Generated.Add
import Generated.Divide
import Generated.Index
import Generated.Shift
import GotoLean.Audit

/-! Feasible-input witnesses, not input/branch coverage. Each admitted row returns normally.
The same rows are sent to compiled C by compare.py; no invalid C execution is requested. -/
namespace CheckCases
open GotoLean

-- Twenty distinct signed inputs. Add admits INT_MIN but excludes INT_MAX.
def signed : List (String × Int) := [
  ("min", -2147483648), ("min+1", -2147483647), ("large-negative", -1000000),
  ("negative-byte", -256), ("negative-small", -100), ("negative-word", -32),
  ("negative-eight", -8), ("negative-two", -2), ("negative-one", -1), ("zero", 0),
  ("one", 1), ("two", 2), ("seven", 7), ("byte-edge", 127), ("byte", 255),
  ("byte+1", 256), ("large-positive", 1000000), ("max-3", 2147483644),
  ("max-2", 2147483645), ("max-1", 2147483646)]

-- Abs has the opposite endpoint restriction.
def absolute := ("max", 2147483647) :: signed.drop 1

-- Four cases exhaust this example's admitted index domain; duplicates would add no coverage.
def indices : List (String × Int) := [("first", 0), ("second", 1), ("third", 2), ("last", 3)]

-- name, numerator, divisor (signed division truncates towards zero).
def division : List (String × Int × Int) := [
  ("zero-positive", 0, 1), ("zero-negative", 0, -1), ("one", 1, 1), ("negative-one", -1, 1),
  ("both-negative", -1, -1), ("positive-negative", 1, -1), ("truncate-positive", 7, 3),
  ("truncate-negative", -7, 3), ("negative-divisor", 7, -3), ("both-truncate", -7, -3),
  ("min-identity", -2147483648, 1), ("min-half", -2147483648, 2),
  ("min-negative-half", -2147483648, -2), ("min-by-min", -2147483648, -2147483648),
  ("max-identity", 2147483647, 1), ("max-negate", 2147483647, -1),
  ("max-half", 2147483647, 2), ("max-by-min", 2147483647, -2147483648),
  ("small-by-max", 1, 2147483647), ("negative-by-max", -1, 2147483647)]

def shifts : List (String × Int × Int) := [
  ("zero-identity", 0, 0), ("zero-max-distance", 0, 31), ("one-identity", 1, 0),
  ("one-low", 1, 1), ("one-byte-edge", 1, 7), ("one-byte", 1, 8), ("one-half", 1, 16),
  ("one-high", 1, 30), ("one-sign-bit", 1, 31), ("all-identity", 4294967295, 0),
  ("all-low", 4294967295, 1), ("all-half", 4294967295, 16),
  ("all-high", 4294967295, 31), ("high-identity", 2147483648, 0),
  ("high-discarded", 2147483648, 1), ("alternating", 2863311530, 1),
  ("alternating-high", 1431655765, 31), ("byte-half", 255, 16),
  ("byte-high", 255, 24), ("word-high", 65535, 16)]

private def bits (x : Int) := BitVec.ofInt 32 x
private def choices := List.replicate 20 0

/-- Every listed add input admits a completed execution, including all reached checks. -/
theorem add : ∀ c ∈ signed, ∃ result,
    Executes v_checked_add.step (v_checked_add.initial (bits c.2)) (.returned result) := by
  apply replay_cases _ (fun f ↦ reprStr f.1) _ _ 10 choices
  decide +kernel

/-- Every listed abs input admits a completed execution. -/
theorem abs : ∀ c ∈ absolute, ∃ result,
    Executes v_checked_abs.step (v_checked_abs.initial (bits c.2)) (.returned result) := by
  apply replay_cases _ (fun f ↦ reprStr f.1) _ _ 10 choices
  decide +kernel

/-- Every admitted index is represented and completes. -/
theorem index : ∀ c ∈ indices, ∃ result,
    Executes v_checked_index.step (v_checked_index.initial (bits c.2)) (.returned result) := by
  apply replay_cases _ (fun f ↦ reprStr f.1) _ _ 10 choices
  decide +kernel

/-- Every listed division input passes both C assumptions and returns. -/
theorem divide : ∀ c ∈ division, ∃ result,
    Executes v_checked_divide.step (v_checked_divide.initial (bits c.2.1) (bits c.2.2))
      (.returned result) := by
  apply replay_cases _ (fun f ↦ reprStr f.1) _ _ 10 choices
  decide +kernel

/-- Every listed unsigned shift is admitted and returns. -/
theorem shift : ∀ c ∈ shifts, ∃ result,
    Executes v_checked_shift.step (v_checked_shift.initial (bits c.2.1) (bits c.2.2))
      (.returned result) := by
  apply replay_cases _ (fun f ↦ reprStr f.1) _ _ 10 choices
  decide +kernel

private def rejected : Outcome α → Bool
  | .assumptionRejected _ => true
  | _ => false

/-- Excluded boundaries remain excluded; a successful proof must not silently erase assumptions. -/
theorem exclusions :
    rejected (v_checked_add.eval 2147483647 10 choices).1 ∧
    rejected (v_checked_abs.eval 2147483648 10 choices).1 ∧
    rejected (v_checked_index.eval 4 10 choices).1 ∧
    rejected (v_checked_divide.eval 1 0 10 choices).1 ∧
    rejected (v_checked_divide.eval 2147483648 4294967295 10 choices).1 ∧
    rejected (v_checked_shift.eval 1 32 10 choices).1 := by decide +kernel

#guard signed.length == 20 && absolute.length == 20 && indices.length == 4 &&
  division.length == 20 && shifts.length == 20
#check_axioms add
#check_axioms abs
#check_axioms index
#check_axioms divide
#check_axioms shift
#check_axioms exclusions

-- One input table drives both the certificates above and native/Lean comparison.
def main : IO Unit := do
  let emit (function name : String) (x y : Int) (out : Outcome (BitVec 32)) := do
    let .returned value := out | throw (IO.userError s!"{function}/{name} did not return")
    IO.println s!"{function} {name} {x} {y} {value.toNat}"
  for (name, x) in signed do emit "checked_add" name x 0 (v_checked_add.eval (bits x) 10 choices).1
  for (name, x) in absolute do
    emit "checked_abs" name x 0 (v_checked_abs.eval (bits x) 10 choices).1
  for (name, x) in indices do
    emit "checked_index" name x 0 (v_checked_index.eval (bits x) 10 choices).1
  for (name, x, y) in division do
    emit "checked_divide" name x y (v_checked_divide.eval (bits x) (bits y) 10 choices).1
  for (name, x, y) in shifts do
    emit "checked_shift" name x y (v_checked_shift.eval (bits x) (bits y) 10 choices).1

end CheckCases

def main := CheckCases.main
