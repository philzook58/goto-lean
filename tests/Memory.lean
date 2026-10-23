import GotoLean.Audit
import CursorAlias
import StableUninitialized
import NullBad
import BoundsBad
import DeadBad
import StoreParameter
import CursorParameter
import EscapeLocal
import GotoLean.MemoryLemmas
import GotoLean.MemoryViews

open GotoLean Std.WP Lean.Order
set_option experimental.vcgen true

-- Arbitrary declaration contents remain stable, and overwritten choices are still consumed.
#guard (v_stable_uninitialized.eval 10 [12345, 0]).1 matches .returned (1, _)
#guard (v_cursor_alias.eval 10 [16777215, 18446744073709551615, 123]).1
  matches .returned (98, _)
#guard (v_cursor_alias.eval 10 [0, 0]).1 matches .choiceError _
#guard (v_null_bad.eval 10 [0]).1 matches .assertionFailed _
#guard (v_store_parameter.eval 0 123 10 []).1 matches .assertionFailed _
#guard (v_bounds_bad.eval 10 [0, 0]).1 matches .assertionFailed _
#guard (v_dead_bad.eval 10 [0, 0]).1 matches .assertionFailed _

-- The caller supplies shared objects. A store is observable in the returned memory.
private def wordMemory : Memory := { objects := #[none, none, some #[0, 0, 0, 0]] }
private def wordPointer : BitVec 64 := Pointer.make 56 2 0
#guard (v_store_parameter.eval wordPointer 305419896 10 [] wordMemory).1 matches
  .returned (305419896, { objects := #[none, none, some #[120, 86, 52, 18]], globals := [] })

private def cursorMemory : Memory :=
  { objects := #[none, none, some #[97, 98, 0], some (Memory.unpack wordPointer)] }
private def cursorPointer : BitVec 64 := Pointer.make 56 3 0
#guard (v_cursor_parameter.eval cursorPointer 10 [] cursorMemory).1 matches
  .returned (98, _)
#guard (v_cursor_parameter.eval cursorPointer 10 [] cursorMemory).1 ==
  .returned (98, { objects := #[none, none, some #[97, 98, 0],
    some (Memory.unpack (Pointer.add 56 wordPointer 1))] })

#guard Pointer.add 56 (Pointer.make 56 7 (-1) : BitVec 64) 1 == Pointer.make 56 7 0
#guard !Pointer.compare 56 false wordPointer cursorPointer
#guard (pointerDifference "different objects" 56 64 1 wordPointer cursorPointer).eval [73] ==
  (.returned 73, [])

-- Returning a local address does not extend its lifetime.
#guard match (v_escape_local.eval 10 [0]).1 with
  | .returned (p, m) => !m.valid 56 p 1
  | _ => false

namespace MemoryProofs

/-- The ordinary vcgen rule proves that any valid store preserves a distinct object. -/
theorem store_frame (m : Memory) (offsetBits other : Nat) (p : BitVec pw)
    (value : BitVec w) (valid : m.valid offsetBits p ((w + 7) / 8) = true)
    (separate : Pointer.object offsetBits p ≠ other) :
    ⦃True⦄ m.store "frame" offsetBits p value
      ⦃fun m' => m'.bytes other = m.bytes other⦄ := by
  vcgen
  exact ⟨valid, Memory.bytes_put_other m _ other _ separate⟩

/-- A concrete, kernel-checked execution of the original char** probe. -/
theorem cursor_execution : ∃ m,
    Executes v_cursor_alias.step (v_cursor_alias.initial)
      (.returned (98, m)) := by
  have h := evalLoop_exec v_cursor_alias.step (fun frame => reprStr frame.1)
    10 v_cursor_alias.initial [0, 0, 0]
  have evaluated : (evalLoop v_cursor_alias.step (fun frame => reprStr frame.1)
      10 v_cursor_alias.initial [0, 0, 0]).1 =
      .returned (98, { objects := #[none, none, none, none] }) := by decide +kernel
  rw [evaluated] at h
  exact ⟨_, h⟩

/-- A null dereference has a checked reachable failure and refutes the translated safety WP. -/
theorem null_counterexample :
    (∃ site, Executes v_null_bad.step v_null_bad.initial (.assertionFailed site)) ∧
    ¬ v_null_bad.run.wp (fun _ => True) := by
  exact failure_refutes v_null_bad.step (fun frame => reprStr frame.1)
    v_null_bad.initial 10 [0] (by decide) (fun _ => True)

theorem bounds_failure : (v_bounds_bad.eval 10 [0, 0]).1.isAssertionFailure = true := by
  decide +kernel

theorem dead_failure : (v_dead_bad.eval 10 [0, 0]).1.isAssertionFailure = true := by
  decide +kernel

#check_axioms cursor_execution
#check_axioms store_frame
#check_axioms null_counterexample
#check_axioms bounds_failure
#check_axioms dead_failure
#check_axioms Memory.readByte_writeByte
#check_axioms Memory.readByte_writeByte_other
#check_axioms Memory.readByte_writeByte_disjoint
#check_axioms Memory.readBits_writeBits_byte
#check_axioms Memory.store_load_byte
#check_axioms Memory.readByte_copied
#check_axioms Memory.copied_extent
#check_axioms Memory.store_byte_wp
#check_axioms Memory.readBits_writeBits_word
#check_axioms Memory.valueAt_written
#check_axioms Memory.readByte_written_frame

end MemoryProofs
