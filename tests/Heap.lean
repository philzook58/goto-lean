import GotoLean.Audit
import GotoLean.Termination
import HeapRelease
import HeapRoundtrip
import HeapNull
import HeapDead
import HeapDoubleFree
import HeapInterior
import HeapBounds
import HeapStack
import HeapUnchecked

open GotoLean
namespace HeapProofs

-- Allocation must retain arbitrary initial bytes, including a nonzero pattern.
#guard match (Memory.malloc "bytes" 56 8 {} 1).eval [1, 165] with
  | (.returned (_, m), []) => m.bytes 2 == some #[165]
  | _ => false
#guard match (Memory.malloc "empty" 56 8 {} 0).eval [1, 0] with
  | (.returned (p, m), []) =>
    match (Memory.free "empty" 56 m p).eval [] with
    | (.returned after, []) => after.bytes 2 == none
    | _ => false
  | _ => false
#guard ((Memory.malloc "capacity" 56 8
  { objects := Array.replicate 256 none } 1).eval [1]).1.isAssertionFailure

/-- Every input returns unchanged and no live allocation remains, whether malloc fails
or succeeds and regardless of its arbitrary initial bytes. No C assumptions are needed. -/
theorem release_caller (x : BitVec 32) :
    finishes v_heap_release.step 2 (v_heap_release.initial x)
      (fun (result, after) ↦ result = x ∧ after.bytes 2 = none) := by
  simp only [finishes, v_heap_release.step, v_heap_release.initial, Bind.bind,
    Action.wp_bind, Action.wp_pure, Memory.malloc, choose, Action.wp]
  intro first second succeeds
  split <;>
    simp [Memory.allocate, Memory.free, choose, check, Bind.bind, Action.wp_bind,
      Action.wp_pure, Action.wp,
      Memory.bytes, Memory.release, Memory.setGlobal, Pointer.make, Pointer.object,
      Pointer.offset, v_heap_release.offsetBits, v_heap_release.objectBits, shiftLeft_eq]

#check_axioms release_caller

-- Successful execution includes the source assertion, return value, and released allocation.
theorem roundtrip : ∃ m,
    Executes v_heap_roundtrip.step (v_heap_roundtrip.initial 41) (.returned (41, m)) := by
  have h := evalLoop_exec v_heap_roundtrip.step (fun f ↦ reprStr f.1)
    20 (v_heap_roundtrip.initial 41) [0, 0, 1, 4294967295, 0]
  have result : (v_heap_roundtrip.eval 41 20 [0, 0, 1, 4294967295, 0]).1 =
      .returned (41, {
        objects := #[none, none, none]
        heap := [2]
        globals := [("__CPROVER_deallocated", (Pointer.make 56 2 0 : BitVec 64).toNat)] }) := by
    decide +kernel
  rw [show (evalLoop v_heap_roundtrip.step (fun f ↦ reprStr f.1)
    20 (v_heap_roundtrip.initial 41) [0, 0, 1, 4294967295, 0]).1 = _ from result] at h
  exact ⟨_, h⟩

theorem allocation_failure :
    Executes v_heap_roundtrip.step (v_heap_roundtrip.initial 41) (.returned (0, {})) := by
  have h := evalLoop_exec v_heap_roundtrip.step (fun f ↦ reprStr f.1)
    20 (v_heap_roundtrip.initial 41) [0, 0, 0]
  have result : (v_heap_roundtrip.eval 41 20 [0, 0, 0]).1 = .returned (0, {}) := by decide +kernel
  rw [show (evalLoop v_heap_roundtrip.step (fun f ↦ reprStr f.1)
    20 (v_heap_roundtrip.initial 41) [0, 0, 0]).1 = _ from result] at h
  exact h

/-- Every memory is unchanged by free(NULL). -/
theorem free_null (m : Memory) : Memory.free "null" 56 m (0 : BitVec 64) = pure m := by
  simp [Memory.free]

-- Each witness refutes safety, not merely a printed replay result.
theorem use_after_free :
    (∃ site, Executes v_heap_dead.step (v_heap_dead.initial 1) (.assertionFailed site)) ∧
    ¬ (v_heap_dead.run 1).wp (fun _ ↦ True) := by
  exact failure_refutes _ (fun f ↦ reprStr f.1) _ 20 [0, 0, 1, 0] (by decide +kernel) _

theorem double_free :
    (∃ site, Executes v_heap_double_free.step v_heap_double_free.initial (.assertionFailed site)) ∧
    ¬ v_heap_double_free.run.wp (fun _ ↦ True) := by
  exact failure_refutes _ (fun f ↦ reprStr f.1) _ 20 [0, 0, 1, 0] (by decide +kernel) _

theorem interior_free :
    (∃ site, Executes v_heap_interior.step v_heap_interior.initial (.assertionFailed site)) ∧
    ¬ v_heap_interior.run.wp (fun _ ↦ True) := by
  exact failure_refutes _ (fun f ↦ reprStr f.1) _ 20 [0, 0, 1, 0] (by decide +kernel) _

theorem outside_object :
    (∃ site, Executes v_heap_bounds.step v_heap_bounds.initial (.assertionFailed site)) ∧
    ¬ v_heap_bounds.run.wp (fun _ ↦ True) := by
  exact failure_refutes _ (fun f ↦ reprStr f.1) _ 20 [0, 0, 1, 0] (by decide +kernel) _

theorem stack_free :
    (∃ site, Executes v_heap_stack.step v_heap_stack.initial (.assertionFailed site)) ∧
    ¬ v_heap_stack.run.wp (fun _ ↦ True) := by
  exact failure_refutes _ (fun f ↦ reprStr f.1) _ 20 [0] (by decide +kernel) _

theorem unchecked_failure :
    (∃ site, Executes v_heap_unchecked.step v_heap_unchecked.initial (.assertionFailed site)) ∧
    ¬ v_heap_unchecked.run.wp (fun _ ↦ True) := by
  exact failure_refutes _ (fun f ↦ reprStr f.1) _ 20 [0, 0, 0] (by decide +kernel) _

#check_axioms roundtrip
#check_axioms allocation_failure
#check_axioms free_null
#check_axioms use_after_free
#check_axioms double_free
#check_axioms interior_free
#check_axioms outside_object
#check_axioms stack_free
#check_axioms unchecked_failure
end HeapProofs
