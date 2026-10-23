import GotoLean.Audit
import Checked

/-! Kernel-checked successful executions of all seven instrumented algorithms.
These are concrete certificates; the general array contracts are in `Spec.lean`.
Every source/property check reached on each execution must succeed. -/
namespace ArrayExamples.CheckedExecutions
open GotoLean

def memory : Memory :=
  { objects := #[none, none,
      some (([3, 1, 2, 1] : List (BitVec 32)).flatMap
        (fun v ↦ (Memory.unpack v).toList)).toArray] }
def sortedMemory : Memory :=
  { objects := #[none, none,
      some (([1, 1, 2, 3] : List (BitVec 32)).flatMap
        (fun v ↦ (Memory.unpack v).toList)).toArray] }
def pointer : BitVec 64 := Pointer.make 56 2 0
private def choices := List.replicate 100 0
private def returned (out : Outcome α) : Bool :=
  match out with | .returned _ => true | _ => false

/-- A successful replay certifies a finite execution of the translated blocks. -/
private theorem certificate (step : Step σ α) (describe : σ → String)
    (fuel : Nat) (initial : σ) (choices : List Nat)
    (success : returned (evalLoop step describe fuel initial choices).1 = true) :
    ∃ result, Executes step initial (.returned result) := by
  have execution := evalLoop_exec step describe fuel initial choices
  cases h : (evalLoop step describe fuel initial choices).1 <;>
    simp [h, returned] at success
  exact ⟨_, by simpa [h, Outcome.Corresponds] using execution⟩

-- Kernel reduction, without a native-checking axiom.

/-- All reached checks pass for this fill execution. -/
theorem fill : ∃ result,
    Executes v_fill.step (v_fill.initial pointer 4 9 memory) (.returned result) := by
  apply certificate _ (fun frame ↦ reprStr frame.1) 200 _ choices
  decide +kernel

#check_axioms fill

/-- All reached checks pass for this find execution. -/
theorem find : ∃ result,
    Executes v_find.step (v_find.initial pointer 4 1 memory) (.returned result) := by
  apply certificate _ (fun frame ↦ reprStr frame.1) 200 _ choices
  decide +kernel

#check_axioms find

/-- All reached checks pass for this is_sorted_until execution. -/
theorem is_sorted_until : ∃ result,
    Executes v_is_sorted_until.step (v_is_sorted_until.initial pointer 4 memory) (.returned result) := by
  apply certificate _ (fun frame ↦ reprStr frame.1) 200 _ choices
  decide +kernel

#check_axioms is_sorted_until

/-- All reached checks pass for this rotate execution. -/
theorem rotate : ∃ result,
    Executes v_rotate.step (v_rotate.initial pointer 2 4 memory) (.returned result) := by
  apply certificate _ (fun frame ↦ reprStr frame.1) 200 _ choices
  decide +kernel

#check_axioms rotate

/-- All reached checks pass for this bubble_sort execution. -/
theorem bubble_sort : ∃ result,
    Executes v_bubble_sort.step (v_bubble_sort.initial pointer 4 memory) (.returned result) := by
  apply certificate _ (fun frame ↦ reprStr frame.1) 200 _ choices
  decide +kernel

#check_axioms bubble_sort

/-- All reached checks pass for this lower_bound execution. -/
theorem lower_bound : ∃ result,
    Executes v_lower_bound.step (v_lower_bound.initial pointer 4 2 sortedMemory) (.returned result) := by
  apply certificate _ (fun frame ↦ reprStr frame.1) 200 _ choices
  decide +kernel

#check_axioms lower_bound

/-- All reached checks pass for this reverse execution. -/
theorem reverse : ∃ result,
    Executes v_reverse.step (v_reverse.initial pointer 4 memory) (.returned result) := by
  apply certificate _ (fun frame ↦ reprStr frame.1) 200 _ choices
  decide +kernel

#check_axioms reverse

/-- CPROVER state is read at runtime: marking the array dead really fails its check. -/
theorem dead_object_failure :
    (∃ site, Executes v_fill.step
      (v_fill.initial pointer 4 9 (memory.setGlobal "__CPROVER_dead_object" pointer))
      (.assertionFailed site)) ∧
    ¬ (v_fill.run pointer 4 9
      (memory.setGlobal "__CPROVER_dead_object" pointer)).wp (fun _ ↦ True) := by
  exact failure_refutes v_fill.step (fun frame ↦ reprStr frame.1)
    _ 200 [0] (by decide +kernel) (fun _ ↦ True)

#check_axioms dead_object_failure

end ArrayExamples.CheckedExecutions
