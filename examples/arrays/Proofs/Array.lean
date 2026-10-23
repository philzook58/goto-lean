import Spec.Array
import GotoLean.PointerLemmas

namespace ArrayExamples
open GotoLean

/-- The zero extension in CBMC's array-index expression preserves every unsigned index. -/
theorem index_address (p : BitVec 64) (i : BitVec 32) :
    Pointer.add 56 p ((0 + (i.setWidth 64).toInt) * 4) = address p i.toNat := by
  have hi := i.isLt
  have hz : (i.setWidth 64).toInt = Int.ofNat i.toNat := by
    rw [BitVec.toInt_eq_toNat_of_lt (by simp; omega)]
    simp only [BitVec.toNat_setWidth, Int.ofNat_eq_natCast]
    omega
  simp [hz, address, Int.mul_comm]

end ArrayExamples

namespace ArrayExamples
open GotoLean

/-- An int store preserves a disjoint int, including within the same allocation. -/
theorem valueAt_frame (m : Memory) (p q : BitVec 64) (v x : BitVec 32)
    (hp : m.valid 56 p 4 = true) (hq : m.ValueAt 56 q x)
    (apart : Pointer.object 56 p ≠ Pointer.object 56 q ∨
      Pointer.offset 56 q + 4 ≤ Pointer.offset 56 p ∨
      Pointer.offset 56 p + 4 ≤ Pointer.offset 56 q) :
    (m.written 56 p v).ValueAt 56 q x := by
  constructor
  · rw [Memory.valid_of_extent m _ (Memory.written_extent m 56 p v hp)]
    exact hq.1
  · by_cases ho : Pointer.object 56 p = Pointer.object 56 q
    · obtain ⟨b, hb, _, _⟩ := (Memory.valid_iff ..).mp hp
      have hbyte (j : Nat) (hj : j < 4) :
          (Memory.writeBits b (Pointer.offset 56 p) v)[Pointer.offset 56 q + j]? =
            b[Pointer.offset 56 q + j]? := by
        apply Memory.getElem?_writeBits_frame
        simp only [Nat.reduceAdd, Nat.reduceDiv]
        rcases apart with h | h | h
        · exact (h ho).elim
        · left; omega
        · right; omega
      simp only [Memory.ValueAt] at hq
      rw [← hq.2]
      simp only [Memory.written, ← ho,
        Memory.bytes_put m _ _ (Memory.bytes_bound m _ b hb), hb, Option.getD_some]
      simp only [Memory.readBits, List.range_succ, List.range_zero, List.foldl_append,
        List.foldl_cons, List.foldl_nil]
      rw [hbyte 0 (by decide), hbyte 1 (by decide), hbyte 2 (by decide), hbyte 3 (by decide)]
    · simpa only [Memory.bytes_written_other m 56 p v _ ho] using hq.2

/-- A store into element `i` updates exactly that element of the array view. -/
theorem wordsAt_written (m : Memory) (p : BitVec 64) (n : Nat) (xs : Values)
    (mem : WordsAt m p n xs) (nowrap : Pointer.offset 56 p + 4 * n < 2^56)
    (i : Nat) (hi : i < n) (v : BitVec 32) :
    WordsAt (m.written 56 (address p i) v) p n (fun j ↦ if j = i then v else xs j) := by
  intro j hj
  by_cases eq : j = i
  · subst j
    simpa using Memory.valueAt_written m 56 (address p i) v (Or.inl rfl) (mem i hi).1
  · simp only [eq, ↓reduceIte]
    apply valueAt_frame m _ _ v _ (mem i hi).1 (mem j hj)
    right
    have offsets (k : Nat) (hk : k < n) :
        Pointer.offset 56 (address p k) = Pointer.offset 56 p + 4*k :=
      Pointer.offset_add_nat p (4*k) (by decide) (by omega)
    rw [offsets i hi, offsets j hj]
    omega

theorem frame_refl (m : Memory) (p : BitVec 64) (n : Nat) : Frame m m p n := by
  intro object offset outside; rfl

theorem frame_written (before m : Memory) (p : BitVec 64) (n : Nat)
    (frame : Frame before m p n) (i : Nat) (hi : i < n)
    (nowrap : Pointer.offset 56 p + 4*n < 2^56) (v : BitVec 32)
    (valid : m.valid 56 (address p i) 4 = true) :
    Frame before (m.written 56 (address p i) v) p n := by
  intro object offset outside
  rw [Memory.readByte_written_frame m 56 (address p i) v valid object offset ?_]
  · exact frame object offset outside
  · simp only [address, Pointer.object_add]
    rw [Pointer.offset_add_nat p (4*i) (by decide) (by omega)]
    rcases outside with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl (by omega))
    · exact Or.inr (Or.inr (by omega))

end ArrayExamples

namespace ArrayExamples

/-- Unsigned loop indices agree with natural-number increment while below their bound. -/
theorem index_increment (i n : BitVec 32) (h : i.toNat < n.toNat) :
    (i+1).toNat = i.toNat+1 := by
  apply BitVec.toNat_add_of_lt
  have := n.isLt
  change i.toNat+1 < 2^32
  omega

theorem index_predecessor (i : BitVec 32) (h : 0 < i.toNat) :
    (i-1).toNat = i.toNat-1 :=
  BitVec.toNat_sub_of_le (by simp only [BitVec.le_def]; change 1 ≤ i.toNat; omega)

end ArrayExamples
