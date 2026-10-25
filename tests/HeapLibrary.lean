import GotoLean.Audit
import LibraryRoundtrip
import LibraryCalloc
import LibraryCallocOverflow
import LibraryDoubleFree
import LibraryDead
import PrimitiveZero
import PrimitiveStable
import PrimitiveBad
import PrimitiveNull
import LibraryRealloc
import LibraryReallocNull
import LibraryReallocZero
import LibraryReallocBad
import LibraryReallocOld
import CopyPaddingBad
import ShortCircuit

/-! Executions of CBMC's loaded library bodies and their imported checks.
Unlike the external free model, CBMC's body nondeterministically records deallocation;
we retain that choice and do not erase the object's bytes. -/
namespace HeapLibraryProofs
open GotoLean

-- Choice 4 is malloc failure; 15 records the freed object; 2 supplies initial primitive bytes.
private def zeros := List.replicate 100 0
private def returnsValue (expected : BitVec 32) : Outcome (BitVec 32 × Memory) → Bool
  | .returned (value, _) => value == expected
  | _ => false

private theorem returned (step : Step σ (BitVec 32 × Memory)) (describe : σ → String)
    (initial : σ) (choices : List Nat) (expected : BitVec 32)
    (ok : returnsValue expected (evalLoop step describe 100 initial choices).1 = true) :
    ∃ m, Executes step initial (.returned (expected, m)) := by
  have execution := evalLoop_exec step describe 100 initial choices
  cases h : (evalLoop step describe 100 initial choices).1 <;> simp [h, returnsValue] at ok
  rename_i value
  rcases value with ⟨result, m⟩
  change result = expected at ok
  subst result
  exact ⟨m, by simpa [h, Outcome.Corresponds] using execution⟩

/-- The loaded malloc/free bodies pass the caller assertion and return 41. -/
theorem roundtrip : ∃ m,
    Executes v_library_roundtrip.step (v_library_roundtrip.initial 41) (.returned (41, m)) := by
  exact returned _ (fun f ↦ reprStr f.1) _ zeros 41 (by decide +kernel)

/-- Allocation failure is handled by the C caller, rather than by the allocation primitive. -/
theorem malloc_failure : ∃ m,
    Executes v_library_roundtrip.step (v_library_roundtrip.initial 41) (.returned (0, m)) := by
  exact returned _ (fun f ↦ reprStr f.1) _ (zeros.set 4 1) 0 (by decide +kernel)

/-- The loaded calloc body takes its success branch and checks both zeroed words. -/
theorem calloc_zero : ∃ m,
    Executes v_library_calloc.step v_library_calloc.initial (.returned (1, m)) := by
  exact returned _ (fun f ↦ reprStr f.1) _ zeros 1 (by decide +kernel)

/-- Multiplication overflow returns null before attempting an enormous allocation. -/
theorem calloc_overflow : ∃ m,
    Executes v_library_calloc_overflow.step v_library_calloc_overflow.initial (.returned (1, m)) := by
  exact returned _ (fun f ↦ reprStr f.1) _ zeros 1 (by decide +kernel)

-- The primitive's zero flag consumes no arbitrary-byte choice; nonzero initial bytes stay stable.
#guard returnsValue 0 (v_primitive_zero.eval 100 zeros).1
#guard returnsValue 1 (v_primitive_null.eval 100 zeros).1
#guard returnsValue 165 (v_primitive_stable.eval 100 (zeros.set 2 165)).1

private def hasSuffix (suffix site : String) : Bool :=
  suffix.toUTF8.data.toList.isSuffixOf site.toUTF8.data.toList

private def failedAt (suffix : String) : Outcome α → Bool
  | .assertionFailed site => hasSuffix suffix site
  | _ => false

private theorem failed (step : Step σ α) (describe : σ → String) (initial : σ)
    (choices : List Nat) (suffix : String)
    (ok : failedAt suffix (evalLoop step describe 100 initial choices).1 = true) :
    ∃ site, hasSuffix suffix site = true ∧ Executes step initial (.assertionFailed site) ∧
      ¬ (run step initial).wp (fun _ ↦ True) := by
  have execution := evalLoop_exec step describe 100 initial choices
  have failure := failure_refutes step describe initial 100 choices
    (by cases h : (evalLoop step describe 100 initial choices).1 <;>
          simp [h, failedAt] at ok ⊢; rfl) (fun _ ↦ True)
  cases h : (evalLoop step describe 100 initial choices).1 <;> simp [h, failedAt] at ok
  exact ⟨_, ok, by simpa [h, Outcome.Corresponds] using execution, failure.2⟩

/-- The second free reaches CBMC's imported valid-pointer precondition failure. -/
theorem double_free : ∃ site,
    hasSuffix "; property free.precondition.1; free argument must be NULL or valid pointer" site = true ∧
    Executes v_library_double_free.step v_library_double_free.initial (.assertionFailed site) ∧
    ¬ v_library_double_free.run.wp (fun _ ↦ True) := by
  exact failed _ (fun f ↦ reprStr f.1) _ (zeros.set 15 1) _ (by decide +kernel)

/-- The post-free read reaches the imported deallocated-object check. -/
theorem use_after_free : ∃ site,
    hasSuffix ("; property library_dead.pointer_dereference.9; " ++
      "dereference failure: deallocated dynamic object in *p") site = true ∧
    Executes v_library_dead.step v_library_dead.initial (.assertionFailed site) ∧
    ¬ v_library_dead.run.wp (fun _ ↦ True) := by
  exact failed _ (fun f ↦ reprStr f.1) _ (zeros.set 15 1) _ (by decide +kernel)

/-- Allocation without zero initialization refutes a source assertion that assumes zero. -/
theorem arbitrary_is_not_zero : ∃ site,
    hasSuffix "; property primitive_bad.assertion.1; arbitrary bytes need not be zero" site = true ∧
    Executes v_primitive_bad.step v_primitive_bad.initial (.assertionFailed site) ∧
    ¬ v_primitive_bad.run.wp (fun _ ↦ True) := by
  exact failed _ (fun f ↦ reprStr f.1) _ (zeros.set 2 165) _ (by decide +kernel)

/-- Growing preserves both initialized bytes, including the guarded second-byte assertion. -/
theorem realloc_grows : ∃ m,
    Executes v_library_realloc.step (v_library_realloc.initial 1) (.returned (1, m)) := by
  exact returned _ (fun f ↦ reprStr f.1) _ zeros 1 (by decide +kernel)

/-- Shrinking preserves the retained byte and never evaluates the guarded out-of-bounds read. -/
theorem realloc_shrinks : ∃ m,
    Executes v_library_realloc.step (v_library_realloc.initial 0) (.returned (1, m)) := by
  exact returned _ (fun f ↦ reprStr f.1) _ zeros 1 (by decide +kernel)

/-- Failure of the replacement allocation leaves the original bytes readable and freeable. -/
theorem realloc_failure : ∃ m,
    Executes v_library_realloc.step (v_library_realloc.initial 1) (.returned (2, m)) := by
  exact returned _ (fun f ↦ reprStr f.1) _ (zeros.set 19 1) 2 (by decide +kernel)

#guard returnsValue 1 (v_library_realloc_null.eval 100 zeros).1
#guard returnsValue 1 (v_library_realloc_zero.eval 100 zeros).1
#guard returnsValue 0 (v_short_circuit.eval 0 100 zeros).1
#guard returnsValue 1 (v_short_circuit.eval 1 100 zeros).1

/-- Realloc does not promise to zero its extension. -/
theorem realloc_extension : ∃ site,
    hasSuffix "; property library_realloc_bad.assertion.1; realloc extension need not be zero"
      site = true ∧
    Executes v_library_realloc_bad.step v_library_realloc_bad.initial (.assertionFailed site) ∧
    ¬ v_library_realloc_bad.run.wp (fun _ ↦ True) := by
  exact failed _ (fun f ↦ reprStr f.1) _ (zeros.set 29 1) _ (by decide +kernel)

/-- A successful move makes the old pointer fail the imported deallocation check. -/
theorem realloc_old_pointer : ∃ site,
    hasSuffix ("; property library_realloc_old.pointer_dereference.9; " ++
      "dereference failure: deallocated dynamic object in *p") site = true ∧
    Executes v_library_realloc_old.step v_library_realloc_old.initial (.assertionFailed site) ∧
    ¬ v_library_realloc_old.run.wp (fun _ ↦ True) := by
  exact failed _ (fun f ↦ reprStr f.1) _ (zeros.set 31 1) _ (by decide +kernel)

/-- Copy extension is fresh arbitrary data even when the destination was initialized to zero. -/
theorem copy_padding : ∃ site,
    hasSuffix ("; property copy_padding_bad.assertion.2; " ++
      "array_copy padding need not retain destination bytes") site = true ∧
    Executes v_copy_padding_bad.step v_copy_padding_bad.initial (.assertionFailed site) ∧
    ¬ v_copy_padding_bad.run.wp (fun _ ↦ True) := by
  exact failed _ (fun f ↦ reprStr f.1) _ (zeros.set 2 1) _ (by decide +kernel)

#check_axioms realloc_grows
#check_axioms realloc_shrinks
#check_axioms realloc_failure
#check_axioms realloc_extension
#check_axioms realloc_old_pointer
#check_axioms copy_padding
#check_axioms roundtrip
#check_axioms malloc_failure
#check_axioms calloc_zero
#check_axioms calloc_overflow
#check_axioms double_free
#check_axioms use_after_free
#check_axioms arbitrary_is_not_zero
end HeapLibraryProofs
