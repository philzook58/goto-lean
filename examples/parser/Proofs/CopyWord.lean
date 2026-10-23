import Generated.TakeWord
import GotoLean.MemoryLemmas
import GotoLean.Contracts
import GotoLean.PointerLemmas

/-! Universal contracts for the unchanged generated copy helper. -/
namespace ParserContracts
open GotoLean

private theorem object_add (p : BitVec 64) (bytes : Int) :
    Pointer.object 56 (Pointer.add 56 p bytes) = Pointer.object 56 p := by
  exact Pointer.object_add p bytes

private theorem offset_add (p n : BitVec 64)
    (h : Pointer.offset 56 p + n.toNat < 2 ^ 56) :
    Pointer.offset 56 (Pointer.add 56 p n.toInt) = Pointer.offset 56 p + n.toNat := by
  have hn : n.toInt = (n.toNat : Int) := BitVec.toInt_eq_toNat_of_lt (by omega)
  rw [hn]
  exact Pointer.offset_add_nat p n.toNat (by decide) h

/-- Sufficient length, validity and separation bounds, including pointer-offset arithmetic. -/
structure CopyPre (m : Memory) (out start n capacity : BitVec 64) : Prop where
  length : n.toNat < capacity.toNat
  source : m.valid 56 start n.toNat = true
  destination : m.valid 56 out capacity.toNat = true
  separated : Memory.disjoint 56 out start n.toNat = true
  noWrap : Pointer.offset 56 out + n.toNat < 2 ^ 56

/-- A specification expression for the final memory, using the executable byte operations. -/
def copiedWord (m : Memory) (out start n : BitVec 64) : Memory :=
  (m.copied 56 out start n.toNat).writeByte
    (Pointer.object 56 out) (Pointer.offset 56 out + n.toNat) 0

/-- Contents and frame condition; this statement does not expose the memory implementation. -/
structure CopyPost (before after : Memory) (out start n : BitVec 64) : Prop where
  copied : ∀ i, i < n.toNat →
    after.readByte (Pointer.object 56 out) (Pointer.offset 56 out + i) =
      before.readByte (Pointer.object 56 start) (Pointer.offset 56 start + i)
  terminated : after.readByte (Pointer.object 56 out) (Pointer.offset 56 out + n.toNat) = some 0
  frame : ∀ object i, object ≠ Pointer.object 56 out ∨ i < Pointer.offset 56 out ∨
      Pointer.offset 56 out + n.toNat < i → after.readByte object i = before.readByte object i
  extent : ∀ object, (after.bytes object).map Array.size = (before.bytes object).map Array.size

private theorem terminator_valid (m : Memory) (out start n capacity : BitVec 64)
    (pre : CopyPre m out start n capacity) :
    (m.copied 56 out start n.toNat).valid 56 (Pointer.add 56 out n.toInt) 1 = true := by
  have hd := Memory.valid_mono m 56 out capacity.toNat n.toNat
    (Nat.le_of_lt pre.length) pre.destination
  rw [Memory.valid_of_extent m _ (Memory.copied_extent m 56 out start n.toNat · pre.source hd)]
  have hl := pre.length
  obtain ⟨b, hb, ho, hn⟩ := (Memory.valid_iff ..).mp pre.destination
  apply (Memory.valid_iff ..).mpr
  exact ⟨b, by simpa [object_add] using hb, by simpa [object_add] using ho,
    by rw [offset_add out n pre.noWrap]; omega⟩

/-- Every copied byte, the terminator, and every untouched byte satisfy the source contract. -/
theorem copiedWord_spec (m : Memory) (out start n capacity : BitVec 64)
    (pre : CopyPre m out start n capacity) : CopyPost m (copiedWord m out start n) out start n := by
  have hd := Memory.valid_mono m 56 out capacity.toNat n.toNat
    (Nat.le_of_lt pre.length) pre.destination
  have copy := Memory.readByte_copied m 56 out start n.toNat
  have ext := fun object ↦ Memory.copied_extent m 56 out start n.toNat object pre.source hd
  constructor
  · intro i hi
    unfold copiedWord
    rw [Memory.readByte_writeByte_disjoint _ _ _ _ _ (by omega)]
    rw [copy _ _ pre.source hd, ite_eq_left (by omega)]
    congr 2 <;> omega
  · obtain ⟨b, hb, _, hn⟩ := (Memory.valid_iff ..).mp (terminator_valid m out start n capacity pre)
    rw [object_add] at hb
    rw [offset_add out n pre.noWrap] at hn
    apply Memory.readByte_writeByte _ _ _ (b[Pointer.offset 56 out + n.toNat]'(by omega)) 0
    simp [Memory.readByte, hb, Array.getElem?_eq_getElem (xs := b)
      (i := Pointer.offset 56 out + n.toNat) (by omega)]
  · intro object i hi
    unfold copiedWord
    by_cases ho : Pointer.object 56 out = object
    · subst object
      rw [Memory.readByte_writeByte_disjoint _ _ _ _ _ (by omega), copy _ _ pre.source hd,
        ite_eq_right (by omega)]
    · rw [Memory.readByte_writeByte_other _ _ _ _ _ _ ho, copy _ _ pre.source hd,
        ite_eq_right (by omega)]
  · intro object
    rw [copiedWord, Memory.writeByte_extent]
    exact ext object

/-- A checked summary for every postcondition of the actual generated callee block. -/
theorem copy_word_summary (m : Memory) (out start n capacity : BitVec 64)
    (pre : CopyPre m out start n capacity)
    (Q : Transfer v_take_word.Activation v_take_word.Value → Prop) :
    (v_take_word.body (.v_copy_word
      (v_take_word.Functions.v_copy_word.initial out start n capacity m))).wp Q ↔
      Q (.returned (.v_copy_word ((), copiedWord m out start n))) := by
  have hd := Memory.valid_mono m 56 out capacity.toNat n.toNat
    (Nat.le_of_lt pre.length) pre.destination
  have ht := terminator_valid m out start n capacity pre
  simp only [v_take_word.body, v_take_word.Functions.v_copy_word.initial, Memory.memcpy,
    Bind.bind, Action.wp_bind, check, Action.bind, Action.wp, pre.source, hd, pre.separated,
    true_and, Action.wp_pure]
  rw [Memory.store_byte_wp]
  simp only [show (0 : Int) + n.toInt = n.toInt by omega, Int.mul_one,
    show BitVec.signExtend 8 (0 : BitVec 32) = 0 by decide] at *
  simp [ht, object_add, offset_add out n pre.noWrap, copiedWord]

/-- The original helper satisfies its byte-level contract for every permitted input. -/
theorem copy_word_correct (m : Memory) (out start n capacity : BitVec 64)
    (pre : CopyPre m out start n capacity) :
    (v_take_word.body (.v_copy_word
      (v_take_word.Functions.v_copy_word.initial out start n capacity m))).wp
      (fun transfer ↦ match transfer with
        | .returned (.v_copy_word ((), after)) => CopyPost m after out start n
        | _ => False) := by
  rw [copy_word_summary _ _ _ _ _ pre]
  exact copiedWord_spec m out start n capacity pre

abbrev CallerInvariant :=
  v_take_word.Functions.v_take_word.Frame → (v_take_word.Value → Prop) → Prop

/-- Caller annotations remain separate; the helper is summarized once for all callers. -/
def annotated (caller : CallerInvariant) (frame : v_take_word.Activation)
    (Q : v_take_word.Value → Prop) : Prop :=
  match frame with
  | .v_copy_word (_, s) => CopyPre s.memory s.v_out s.v_start s.v_n s.v_capacity ∧
      Q (.v_copy_word ((), copiedWord s.memory s.v_out s.v_start s.v_n))
  | .v_take_word frame => caller frame Q

private theorem copy_word_block (caller : CallerInvariant)
    (frame : v_take_word.Functions.v_copy_word.Frame) (Q : v_take_word.Value → Prop)
    (hi : annotated caller (.v_copy_word frame) Q) :
    (v_take_word.body (.v_copy_word frame)).wp (Transfer.wp · (annotated caller) Q) := by
  rcases frame with ⟨pc, s⟩
  cases pc
  obtain ⟨pre, hq⟩ := hi
  change (v_take_word.body (.v_copy_word (v_take_word.Functions.v_copy_word.initial
    s.v_out s.v_start s.v_n s.v_capacity s.memory))).wp _
  rw [copy_word_summary _ _ _ _ _ pre]
  exact hq

/-- The actual call site needs the helper precondition and the caller's next-block annotation.
The caller proof never unfolds memcpy, byte stores, or the continuation stack. -/
theorem copy_word_call (caller : CallerInvariant) (s : v_take_word.Functions.v_take_word.Locals)
    (Q : v_take_word.Value → Prop) (pre : CopyPre s.memory s.v_out s.v_start s.v_n s.v_capacity)
    (resumes : caller (.b22, { s with memory := copiedWord s.memory s.v_out s.v_start s.v_n }) Q) :
    (v_take_word.body (.v_take_word (.b20, s))).wp (Transfer.wp · (annotated caller) Q) := by
  refine ⟨(· = .v_copy_word ((), copiedWord s.memory s.v_out s.v_start s.v_n)), ?_, ?_⟩
  · exact ⟨pre, rfl⟩
  · intro value hv
    subst value
    exact resumes

open Std.WP Lean.Order

/-- Proving the caller's annotated blocks establishes the original generated run's contract.
All helper obligations are discharged above; loop annotations belong in `caller`. -/
theorem take_word_rule (caller : CallerInvariant)
    (blocks : ∀ frame post, caller frame post →
      (v_take_word.body (.v_take_word frame)).wp (Transfer.wp · (annotated caller) post))
    (cursor out capacity : BitVec 64) (m : Memory) (Q : v_take_word.Output → Prop)
    (entry : caller (v_take_word.Functions.v_take_word.initial cursor out capacity m)
      (fun value ↦ match value with | .v_take_word result => Q result | _ => False)) :
    (v_take_word.run cursor out capacity m).wp Q := by
  apply (calls_spec v_take_word.body v_take_word.finish (annotated caller)
    (.v_take_word (v_take_word.Functions.v_take_word.initial cursor out capacity m))
    (fun value ↦ match value with | .v_take_word result => Q result | _ => False)
    Q ?_ ?_).le_wp entry
  · intro frame post hi
    cases frame with
    | v_copy_word frame => exact copy_word_block caller frame post hi
    | v_take_word frame => exact blocks frame post hi
  · intro value hv
    cases value with
    | v_copy_word => exact False.elim hv
    | v_take_word => exact hv


end ParserContracts
