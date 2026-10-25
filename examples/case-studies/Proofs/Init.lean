import Spec
import GotoLean.Audit

namespace JsmnProofs
open GotoLean JsmnSpec
set_option autoImplicit false

private def initializedMemory (m : Memory) : Memory :=
  ((m.written 56 parserAddress (0 : BitVec 32)).written 56
    (Pointer.add 56 parserAddress 4) (0 : BitVec 32)).written 56
      (Pointer.add 56 parserAddress 8) (-1 : BitVec 32)

private theorem valid_written (m : Memory) (p : BitVec 64) (v : BitVec 32)
    (h : m.valid 56 p 4 = true) (q : BitVec 64) (n : Nat) :
    (m.written 56 p v).valid 56 q n = m.valid 56 q n :=
  Memory.valid_of_extent m _ (Memory.written_extent m 56 p v h) 56 q n

private theorem objectSize_written (m : Memory) (p : BitVec 64) (v : BitVec 32)
    (h : m.valid 56 p 4 = true) (q : BitVec 64) (site : Site) :
    Memory.objectSize site 56 64 (m.written 56 p v) q = Memory.objectSize site 56 64 m q := by
  have e := Memory.written_extent m 56 p v h (Pointer.object 56 q)
  cases h0 : m.bytes (Pointer.object 56 q) <;>
    cases h1 : (m.written 56 p v).bytes (Pointer.object 56 q) <;>
    simp [h0, h1] at e <;> simp [Memory.objectSize, h0, h1, e]

private theorem globals_written (m : Memory) (p : BitVec 64) (v : BitVec 32)
    (name : String) :
    (m.written 56 p v).getGlobal name (0 : BitVec 64) = m.getGlobal name (0 : BitVec 64) := rfl

private theorem writable (before other : Array (BitVec 8)) (enough : 12 ≤ before.size) :
    let m := initialMemory before other
    m.valid 56 parserAddress 4 = true ∧
    (m.written 56 parserAddress (0 : BitVec 32)).valid 56
      (Pointer.add 56 parserAddress 4) 4 = true ∧
    ((m.written 56 parserAddress (0 : BitVec 32)).written 56
      (Pointer.add 56 parserAddress 4) (0 : BitVec 32)).valid 56
        (Pointer.add 56 parserAddress 8) 4 = true := by
  let m := initialMemory before other
  have hv (n : Nat) (hn : n = 0 ∨ n = 4 ∨ n = 8) :
      m.valid 56 (Pointer.add 56 parserAddress n) 4 = true := by
    rcases hn with rfl | rfl | rfl
    all_goals simp [m, initialMemory, Memory.valid, Memory.bytes, parserAddress,
      Pointer.add, Pointer.make, Pointer.object, Pointer.offset, shiftLeft] <;> omega
  have h0 := hv 0 (by simp)
  change m.valid 56 parserAddress 4 = true at h0
  have h4 := (valid_written m parserAddress 0 h0 (Pointer.add 56 parserAddress 4) 4).trans
    (hv 4 (by simp))
  have h8 := (valid_written m parserAddress 0 h0 (Pointer.add 56 parserAddress 8) 4).trans
    (hv 8 (by simp))
  exact ⟨h0, h4, (valid_written _ _ 0 h4 _ 4).trans h8⟩

private theorem stores_complete (before other : Array (BitVec 8)) (enough : 12 ≤ before.size)
    (fits : before.size < 2^64) :
    finishes v_jsmn_init.step 1 (v_jsmn_init.initial parserAddress (initialMemory before other))
      (fun result ↦ result = ((), initializedMemory (initialMemory before other))) := by
  let m := initialMemory before other
  obtain ⟨h0, h4', h8''⟩ := writable before other enough
  have bound4 : BitVec.ule (4#65) ((BitVec.ofNat 64 before.size).setWidth 65) = true := by
    simp only [BitVec.ule, decide_eq_true_eq, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    change 4 ≤ before.size % 2^64 % 2^65
    omega
  have bound8 : BitVec.ule (8#65) ((BitVec.ofNat 64 before.size).setWidth 65) = true := by
    simp only [BitVec.ule, decide_eq_true_eq, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    change 8 ≤ before.size % 2^64 % 2^65
    omega
  have bound12 : BitVec.ule (12#65) ((BitVec.ofNat 64 before.size).setWidth 65) = true := by
    simp only [BitVec.ule, decide_eq_true_eq, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    change 12 ≤ before.size % 2^64 % 2^65
    omega
  have add0 : Pointer.add 56 parserAddress 0 = parserAddress := by decide
  have extent : m.bytes 2 = some before := by simp [m, initialMemory, Memory.bytes]
  have obj : Pointer.object 56 parserAddress = 2 := by decide
  have globals (key : String) : m.getGlobal key (0 : BitVec 64) = 0 := rfl
  have size0 (site : Site) : Memory.objectSize site 56 64 m parserAddress =
      pure (BitVec.ofNat 64 before.size) := by simp only [Memory.objectSize, obj, extent]
  have size1 (site : Site) : Memory.objectSize site 56 64
      (m.written 56 parserAddress (0 : BitVec 32)) parserAddress =
      pure (BitVec.ofNat 64 before.size) := by rw [objectSize_written _ _ _ h0, size0]
  have size2 (site : Site) : Memory.objectSize site 56 64
      ((m.written 56 parserAddress (0 : BitVec 32)).written 56
        (Pointer.add 56 parserAddress 4) (0 : BitVec 32)) parserAddress =
      pure (BitVec.ofNat 64 before.size) := by rw [objectSize_written _ _ _ h4', size1]
  simp only [finishes, v_jsmn_init.step, v_jsmn_init.initial, Bind.bind, Action.wp_bind,
    Pure.pure, v_jsmn_init.offsetBits, add0, Memory.store_wp,
    globals_written, h0, h4', h8'']
  simp only [check, Action.wp, initializedMemory]
  simp_all [m, parserAddress, Pointer.object, Pointer.add, Pointer.make, shiftLeft,
    initialMemory, Memory.getGlobal]

private theorem fields (before other : Array (BitVec 8)) (enough : 12 ≤ before.size) :
    let after := initializedMemory (initialMemory before other)
    after.ValueAt 56 parserAddress (0 : BitVec 32) ∧
    after.ValueAt 56 (Pointer.add 56 parserAddress 4) (0 : BitVec 32) ∧
    after.ValueAt 56 (Pointer.add 56 parserAddress 8) (-1 : BitVec 32) := by
  obtain ⟨h0, h4, h8⟩ := writable before other enough
  have pos := Memory.valueAt_written (initialMemory before other) 56 parserAddress
    (0 : BitVec 32) (by simp) h0
  have next := Memory.valueAt_written _ 56 (Pointer.add 56 parserAddress 4)
    (0 : BitVec 32) (by simp) h4
  have pos' := Memory.valueAt_written_disjoint _ 56 (Pointer.add 56 parserAddress 4)
    parserAddress (0 : BitVec 32) 0 h4 pos (by decide)
  exact ⟨Memory.valueAt_written_disjoint _ 56 (Pointer.add 56 parserAddress 8)
      parserAddress (-1 : BitVec 32) 0 h8 pos' (by decide),
    Memory.valueAt_written_disjoint _ 56 (Pointer.add 56 parserAddress 8)
      (Pointer.add 56 parserAddress 4) (-1 : BitVec 32) 0 h8 next (by decide),
    Memory.valueAt_written _ 56 (Pointer.add 56 parserAddress 8)
      (-1 : BitVec 32) (by simp) h8⟩

private theorem frame (before other : Array (BitVec 8)) (enough : 12 ≤ before.size)
    (object offset : Nat) (outside : object ≠ 2 ∨ 12 ≤ offset) :
    (initializedMemory (initialMemory before other)).readByte object offset =
      (initialMemory before other).readByte object offset := by
  obtain ⟨h0, h4, h8⟩ := writable before other enough
  have out (n : Nat) (hn : n = 0 ∨ n = 4 ∨ n = 8) :
      object ≠ Pointer.object 56 (Pointer.add 56 parserAddress n) ∨
      offset < Pointer.offset 56 (Pointer.add 56 parserAddress n) ∨
      Pointer.offset 56 (Pointer.add 56 parserAddress n) + 4 ≤ offset := by
    rcases hn with rfl | rfl | rfl
    all_goals simp [parserAddress, Pointer.object, Pointer.offset, Pointer.add,
      Pointer.make, shiftLeft] <;> omega
  have out0 := out 0 (by simp)
  change object ≠ Pointer.object 56 parserAddress ∨ offset < Pointer.offset 56 parserAddress ∨
    Pointer.offset 56 parserAddress + 4 ≤ offset at out0
  let m := initialMemory before other
  let m1 := m.written 56 parserAddress (0 : BitVec 32)
  let m2 := m1.written 56 (Pointer.add 56 parserAddress 4) (0 : BitVec 32)
  exact (Memory.readByte_written_frame m2 56 (Pointer.add 56 parserAddress 8)
    (-1 : BitVec 32) h8 object offset (out 8 (by simp))).trans
      ((Memory.readByte_written_frame m1 56 (Pointer.add 56 parserAddress 4)
        (0 : BitVec 32) h4 object offset (out 4 (by simp))).trans
          (Memory.readByte_written_frame m 56 parserAddress (0 : BitVec 32)
            h0 object offset out0))


/-- Positive completion contract for the fully instrumented generated initializer. -/
theorem initialize_completes : JsmnSpec.init := by
  intro before other enough fits
  have completes := stores_complete before other enough fits
  unfold finishes at completes ⊢
  apply Action.wp_mono _ _ completes
  intro outcome h
  cases outcome with
  | inl next => exact False.elim h
  | inr result =>
    change result = ((), initializedMemory (initialMemory before other)) at h
    subst result
    exact ⟨fields before other enough, frame before other enough⟩

#check_axioms initialize_completes
end JsmnProofs
