import Cases.Inputs
import Checked

namespace ArrayExamples.Cases
open GotoLean

/-- Each fill input passes the imported checks and returns normally. -/
theorem fill : ∀ c ∈ cases, ∃ result,
    Executes v_fill.step (v_fill.initial pointer (length c) (bits c.key) (memory c))
      (.returned result) := by
  apply replay_cases _ (fun f ↦ reprStr f.1) _ _ 200 choices
  simp only [cases, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  repeat' apply And.intro
  all_goals decide +kernel

/-- Each find input passes the imported checks and returns normally. -/
theorem find : ∀ c ∈ cases, ∃ result,
    Executes v_find.step (v_find.initial pointer (length c) (bits c.key) (memory c))
      (.returned result) := by
  apply replay_cases _ (fun f ↦ reprStr f.1) _ _ 200 choices
  simp only [cases, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  repeat' apply And.intro
  all_goals decide +kernel

/-- Each prefix input passes the imported checks and returns normally. -/
theorem sorted_prefix : ∀ c ∈ cases, ∃ result,
    Executes v_is_sorted_until.step (v_is_sorted_until.initial pointer (length c) (memory c))
      (.returned result) := by
  apply replay_cases _ (fun f ↦ reprStr f.1) _ _ 200 choices
  simp only [cases, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  repeat' apply And.intro
  all_goals decide +kernel

/-- Each reverse input passes the imported checks and returns normally. -/
theorem reverse : ∀ c ∈ cases, ∃ result,
    Executes v_reverse.step (v_reverse.initial pointer (length c) (memory c))
      (.returned result) := by
  apply replay_cases _ (fun f ↦ reprStr f.1) _ _ 200 choices
  simp only [cases, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  repeat' apply And.intro
  all_goals decide +kernel

/-- Each valid endpoint/interior pivot admits a completed rotation. -/
theorem rotate : ∀ c ∈ cases, ∃ result,
    Executes v_rotate.step
      (v_rotate.initial pointer (.ofNat 32 c.pivot) (length c) (memory c)) (.returned result) := by
  apply replay_cases _ (fun f ↦ reprStr f.1) _ _ 200 choices
  simp only [cases, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  repeat' apply And.intro
  all_goals decide +kernel

/-- Each sort input passes the imported checks and returns normally. -/
theorem sort : ∀ c ∈ cases, ∃ result,
    Executes v_bubble_sort.step (v_bubble_sort.initial pointer (length c) (memory c))
      (.returned result) := by
  apply replay_cases _ (fun f ↦ reprStr f.1) _ _ 200 choices
  simp only [cases, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  repeat' apply And.intro
  all_goals decide +kernel

/-- Each sorted search input passes the imported checks and returns normally. -/
theorem search : ∀ c ∈ sortedCases, ∃ result,
    Executes v_lower_bound.step
      (v_lower_bound.initial pointer (length c) (bits c.key) (memory c)) (.returned result) := by
  apply replay_cases _ (fun f ↦ reprStr f.1) _ _ 200 choices
  simp only [sortedCases, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  repeat' apply And.intro
  all_goals decide +kernel

#guard cases.length == 20 && sortedCases.length == 20
#check_axioms premises
#check_axioms sorted
#check_axioms fill
#check_axioms find
#check_axioms sorted_prefix
#check_axioms reverse
#check_axioms rotate
#check_axioms sort
#check_axioms search
end ArrayExamples.Cases
