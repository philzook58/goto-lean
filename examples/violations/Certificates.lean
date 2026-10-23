import GotoLean.Audit
import Generated

/-! Paired controls for imported CBMC properties. Negative theorems name the property,
certify its reachable failure, and refute safety. Positive theorems certify returned
executions of the repaired C. CBMC separately checks repairs for all admitted inputs. -/
namespace ViolationExamples
open GotoLean

-- Byte matching avoids expensive kernel reduction of String.toList on long diagnostics.
private def containsField (field : List UInt8) : List UInt8 → Bool
  | [] => field.isEmpty
  | text@(_ :: rest) => field.isPrefixOf text || containsField field rest

/-- Match an entire property field in the retained CBMC source-site metadata. -/
def hasProperty (property site : String) : Bool :=
  containsField ("; property " ++ property ++ ";").toUTF8.data.toList site.toUTF8.data.toList

/-- The specified imported property fails on a reachable execution, refuting safety. -/
def Violates (step : Step σ α) (initial : σ) (property : String) : Prop :=
  ∃ site, hasProperty property site = true ∧
    Executes step initial (.assertionFailed site) ∧ ¬ (run step initial).wp (fun _ ↦ True)

private def hits (property : String) (out : Outcome α) : Bool :=
  match out with | .assertionFailed site => hasProperty property site | _ => false

private theorem failure (step : Step σ α) (describe : σ → String) (initial : σ)
    (property : String) (fuel : Nat) (choices : List Nat)
    (failed : hits property (evalLoop step describe fuel initial choices).1 = true) :
    Violates step initial property := by
  have execution := evalLoop_exec step describe fuel initial choices
  cases h : (evalLoop step describe fuel initial choices).1 <;> simp [h, hits] at failed
  have refuted := failure_refutes step describe initial fuel choices
    (by simp [h, Outcome.isAssertionFailure]) (fun _ ↦ True)
  exact ⟨_, failed, by simpa [h, Outcome.Corresponds] using execution, refuted.2⟩

private def returns (out : Outcome α) : Bool :=
  match out with | .returned _ => true | _ => false

private theorem success (step : Step σ α) (describe : σ → String) (initial : σ)
    (fuel : Nat) (choices : List Nat)
    (returned : returns (evalLoop step describe fuel initial choices).1 = true) :
    ∃ result, Executes step initial (.returned result) := by
  have execution := evalLoop_exec step describe fuel initial choices
  cases h : (evalLoop step describe fuel initial choices).1 <;> simp [h, returns] at returned
  exact ⟨_, by simpa [h, Outcome.Corresponds] using execution⟩

/-- The buggy C reaches exactly its `assertion.1` violation. -/
theorem maximum_fails :
    Violates v_bug_maximum.step (v_bug_maximum.initial 0 1)
      "bug_maximum.assertion.1" := by
  apply failure _ (fun frame ↦ reprStr frame.1) _ _ 100 [0]
  decide +kernel

/-- The repaired C returns with every reached imported check satisfied. -/
theorem maximum_fixed : ∃ result,
    Executes v_fixed_maximum.step (v_fixed_maximum.initial 0 1) (.returned result) := by
  apply success _ (fun frame ↦ reprStr frame.1) _ 100 (List.replicate 30 0)
  decide +kernel

#check_axioms maximum_fails
#check_axioms maximum_fixed

/-- The buggy C reaches exactly its `overflow.1` violation. -/
theorem add_fails :
    Violates v_bug_add.step (v_bug_add.initial 2147483647)
      "bug_add.overflow.1" := by
  apply failure _ (fun frame ↦ reprStr frame.1) _ _ 100 []
  decide +kernel

/-- The repaired C returns with every reached imported check satisfied. -/
theorem add_fixed : ∃ result,
    Executes v_fixed_add.step (v_fixed_add.initial 2147483647) (.returned result) := by
  apply success _ (fun frame ↦ reprStr frame.1) _ 100 (List.replicate 30 0)
  decide +kernel

#check_axioms add_fails
#check_axioms add_fixed

/-- The buggy C reaches exactly its `overflow.1` violation. -/
theorem negate_fails :
    Violates v_bug_negate.step (v_bug_negate.initial 2147483648)
      "bug_negate.overflow.1" := by
  apply failure _ (fun frame ↦ reprStr frame.1) _ _ 100 []
  decide +kernel

/-- The repaired C returns with every reached imported check satisfied. -/
theorem negate_fixed : ∃ result,
    Executes v_fixed_negate.step (v_fixed_negate.initial 2147483648) (.returned result) := by
  apply success _ (fun frame ↦ reprStr frame.1) _ 100 (List.replicate 30 0)
  decide +kernel

#check_axioms negate_fails
#check_axioms negate_fixed

/-- The buggy C reaches exactly its `division-by-zero.1` violation. -/
theorem divide_zero_fails :
    Violates v_bug_divide_zero.step (v_bug_divide_zero.initial 7 0)
      "bug_divide_zero.division-by-zero.1" := by
  apply failure _ (fun frame ↦ reprStr frame.1) _ _ 100 []
  decide +kernel

/-- The repaired C returns with every reached imported check satisfied. -/
theorem divide_zero_fixed : ∃ result,
    Executes v_fixed_divide_zero.step (v_fixed_divide_zero.initial 7 0) (.returned result) := by
  apply success _ (fun frame ↦ reprStr frame.1) _ 100 (List.replicate 30 0)
  decide +kernel

#check_axioms divide_zero_fails
#check_axioms divide_zero_fixed

/-- The buggy C reaches exactly its `overflow.1` violation. -/
theorem divide_overflow_fails :
    Violates v_bug_divide_overflow.step (v_bug_divide_overflow.initial 2147483648)
      "bug_divide_overflow.overflow.1" := by
  apply failure _ (fun frame ↦ reprStr frame.1) _ _ 100 []
  decide +kernel

/-- The repaired C returns with every reached imported check satisfied. -/
theorem divide_overflow_fixed : ∃ result,
    Executes v_fixed_divide_overflow.step (v_fixed_divide_overflow.initial 2147483648)
      (.returned result) := by
  apply success _ (fun frame ↦ reprStr frame.1) _ 100 (List.replicate 30 0)
  decide +kernel

#check_axioms divide_overflow_fails
#check_axioms divide_overflow_fixed

/-- The buggy C reaches exactly its `undefined-shift.1` violation. -/
theorem shift_fails :
    Violates v_bug_shift.step (v_bug_shift.initial 1 32)
      "bug_shift.undefined-shift.1" := by
  apply failure _ (fun frame ↦ reprStr frame.1) _ _ 100 []
  decide +kernel

/-- The repaired C returns with every reached imported check satisfied. -/
theorem shift_fixed : ∃ result,
    Executes v_fixed_shift.step (v_fixed_shift.initial 1 32) (.returned result) := by
  apply success _ (fun frame ↦ reprStr frame.1) _ 100 (List.replicate 30 0)
  decide +kernel

#check_axioms shift_fails
#check_axioms shift_fixed

/-- The buggy C reaches exactly its `array_bounds.1` violation. -/
theorem index_fails :
    Violates v_bug_index.step (v_bug_index.initial 4)
      "bug_index.array_bounds.1" := by
  apply failure _ (fun frame ↦ reprStr frame.1) _ _ 100 [0]
  decide +kernel

/-- The repaired C returns with every reached imported check satisfied. -/
theorem index_fixed : ∃ result,
    Executes v_fixed_index.step (v_fixed_index.initial 4) (.returned result) := by
  apply success _ (fun frame ↦ reprStr frame.1) _ 100 (List.replicate 30 0)
  decide +kernel

#check_axioms index_fails
#check_axioms index_fixed

/-- The buggy C reaches exactly its `pointer_dereference.1` violation. -/
theorem null_fails :
    Violates v_bug_null.step (v_bug_null.initial)
      "bug_null.pointer_dereference.1" := by
  apply failure _ (fun frame ↦ reprStr frame.1) _ _ 100 [0]
  decide +kernel

/-- The repaired C returns with every reached imported check satisfied. -/
theorem null_fixed : ∃ result,
    Executes v_fixed_null.step (v_fixed_null.initial) (.returned result) := by
  apply success _ (fun frame ↦ reprStr frame.1) _ 100 (List.replicate 30 0)
  decide +kernel

#check_axioms null_fails
#check_axioms null_fixed

/-- The buggy C reaches exactly its `pointer_dereference.2` violation. -/
theorem one_past_fails :
    Violates v_bug_one_past.step (v_bug_one_past.initial)
      "bug_one_past.pointer_dereference.2" := by
  apply failure _ (fun frame ↦ reprStr frame.1) _ _ 100 [0, 0]
  decide +kernel

/-- The repaired C returns with every reached imported check satisfied. -/
theorem one_past_fixed : ∃ result,
    Executes v_fixed_one_past.step (v_fixed_one_past.initial) (.returned result) := by
  apply success _ (fun frame ↦ reprStr frame.1) _ 100 (List.replicate 30 0)
  decide +kernel

#check_axioms one_past_fails
#check_axioms one_past_fixed

/-- The buggy C reaches exactly its `pointer_dereference.1` violation. -/
theorem lifetime_fails :
    Violates v_bug_lifetime.step (v_bug_lifetime.initial)
      "bug_lifetime.pointer_dereference.1" := by
  apply failure _ (fun frame ↦ reprStr frame.1) _ _ 100 [0, 0, 1]
  decide +kernel

/-- The repaired C returns with every reached imported check satisfied. -/
theorem lifetime_fixed : ∃ result,
    Executes v_fixed_lifetime.step (v_fixed_lifetime.initial) (.returned result) := by
  apply success _ (fun frame ↦ reprStr frame.1) _ 100 (List.replicate 30 0)
  decide +kernel

#check_axioms lifetime_fails
#check_axioms lifetime_fixed

/-- The buggy C reaches exactly its `assertion.1` violation. -/
theorem uninitialized_fails :
    Violates v_bug_uninitialized.step (v_bug_uninitialized.initial)
      "bug_uninitialized.assertion.1" := by
  apply failure _ (fun frame ↦ reprStr frame.1) _ _ 100 [1]
  decide +kernel

/-- The repaired C returns with every reached imported check satisfied. -/
theorem uninitialized_fixed : ∃ result,
    Executes v_fixed_uninitialized.step (v_fixed_uninitialized.initial) (.returned result) := by
  apply success _ (fun frame ↦ reprStr frame.1) _ 100 (1 :: List.replicate 30 0)
  decide +kernel

#check_axioms uninitialized_fails
#check_axioms uninitialized_fixed

/-- The buggy C reaches exactly its `array_bounds.1` violation. -/
theorem loop_bound_fails :
    Violates v_bug_loop_bound.step (v_bug_loop_bound.initial)
      "bug_loop_bound.array_bounds.1" := by
  apply failure _ (fun frame ↦ reprStr frame.1) _ _ 100 [0, 0]
  decide +kernel

/-- The repaired C returns with every reached imported check satisfied. -/
theorem loop_bound_fixed : ∃ result,
    Executes v_fixed_loop_bound.step (v_fixed_loop_bound.initial) (.returned result) := by
  apply success _ (fun frame ↦ reprStr frame.1) _ 100 (List.replicate 30 0)
  decide +kernel

#check_axioms loop_bound_fails
#check_axioms loop_bound_fixed

end ViolationExamples
