import GotoLean.Memory

/-! Pointer decomposition and bounded offset arithmetic for the existing representation. -/
namespace GotoLean.Pointer

theorem ext (p q : BitVec w) (ho : object bits p = object bits q)
    (hf : offset bits p = offset bits q) : p = q := by
  apply BitVec.eq_of_toNat_eq
  simp only [object, offset, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
    BitVec.toNat_setWidth] at ho hf
  have hp := Nat.mod_add_div p.toNat (2 ^ bits)
  have hq := Nat.mod_add_div q.toNat (2 ^ bits)
  rw [hf, ho] at hp
  exact hp.symm.trans hq

theorem object_add (p : BitVec w) (bytes : Int) :
    object bits (add bits p bytes) = object bits p := by
  unfold add make object
  simp only [shiftLeft_eq, BitVec.ofNat_toNat]
  generalize BitVec.ofInt bits bytes = delta
  congr 1
  apply BitVec.eq_of_getLsbD_eq
  intro i
  simp [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_setWidth]
  exact fun _ hp ↦ BitVec.lt_of_getLsbD hp

theorem offset_add_nat (p : BitVec w) (i : Nat) (hw : bits ≤ w)
    (h : offset bits p + i < 2 ^ bits) :
    offset bits (add bits p (Int.ofNat i)) = offset bits p + i := by
  have low (high : BitVec w) (low : BitVec bits) :
      ((high <<< bits ||| low.setWidth w).setWidth bits) = low := by
    simp [BitVec.setWidth_shiftLeft_of_le hw, BitVec.shiftLeft_eq_zero (Nat.le_refl bits),
      BitVec.setWidth_setWidth_of_le low hw]
  simp only [add, make, offset, shiftLeft_eq, low, BitVec.toNat_add]
  change (offset bits p + i % 2 ^ bits) % 2 ^ bits = _
  rw [Nat.mod_eq_of_lt (by omega : i < 2 ^ bits), Nat.mod_eq_of_lt h]
  rfl

theorem add_zero (p : BitVec w) (hw : bits ≤ w) : add bits p 0 = p := by
  apply ext (bits := bits)
  · exact object_add p 0
  · simpa using offset_add_nat p 0 hw (by exact (p.setWidth bits).isLt)

theorem add_succ (p : BitVec w) (i : Nat) (hw : bits ≤ w)
    (h : offset bits p + (i + 1) < 2 ^ bits) :
    add bits (add bits p (Int.ofNat i)) 1 = add bits p (Int.ofNat (i + 1)) := by
  apply ext (bits := bits)
  · simp only [object_add]
  · rw [show (1 : Int) = Int.ofNat 1 by rfl, offset_add_nat _ 1 hw (by
      rw [offset_add_nat p i hw (by omega)]; omega),
      offset_add_nat p i hw (by omega), offset_add_nat p (i + 1) hw h]
    omega

end GotoLean.Pointer
