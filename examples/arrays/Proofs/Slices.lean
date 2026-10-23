import Proofs.Array
import Proofs.Reverse

/-! Array subranges used to compose existing reversal contracts. -/
namespace ArrayExamples
open GotoLean

private theorem valueAt_of_bytes (before after : Memory) (p : BitVec 64) (x : BitVec 32)
    (old : before.ValueAt 56 p x)
    (same : ∀ j, j < 4 → after.readByte (Pointer.object 56 p) (Pointer.offset 56 p+j) =
      before.readByte (Pointer.object 56 p) (Pointer.offset 56 p+j)) : after.ValueAt 56 p x := by
  obtain ⟨a, ha, ho, size⟩ := (Memory.valid_iff ..).mp old.1
  have last : after.readByte (Pointer.object 56 p) (Pointer.offset 56 p+3) ≠ none := by
    rw [same 3 (by decide)]
    simp only [Memory.readByte, ha, Option.bind_some]
    rw [Array.getElem?_eq_getElem (by omega)]
    simp
  cases hb : after.bytes (Pointer.object 56 p) with
  | none => simp [Memory.readByte, hb] at last
  | some b =>
    have bound : Pointer.offset 56 p+3 < b.size := by
      by_cases good : Pointer.offset 56 p+3 < b.size
      · exact good
      ·
        have empty := Array.getElem?_eq_none (xs := b) (i := Pointer.offset 56 p+3) (by omega)
        simp [Memory.readByte, hb, empty] at last
    refine ⟨(Memory.valid_iff ..).mpr ⟨b, hb, ho, by omega⟩, ?_⟩
    have eq := old.2
    simp only [Memory.readByte, ha, hb, Option.bind_some] at same
    rw [← eq]
    simp only [ha, hb, Option.getD_some, Memory.readBits, List.range_succ, List.range_zero,
      List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [same 0 (by decide), same 1 (by decide), same 2 (by decide), same 3 (by decide)]

theorem address_slice (p : BitVec 64) (start i : Nat)
    (nowrap : Pointer.offset 56 p + 4*(start+i) < 2^56) :
    address (address p start) i = address p (start+i) := by
  apply Pointer.ext (bits := 56)
  · simp [address, Pointer.object_add]
  · simp only [address]
    rw [Pointer.offset_add_nat (Pointer.add 56 p (Int.ofNat (4*start))) (4*i)
      (bits := 56) (by decide) (by
        rw [Pointer.offset_add_nat p (4*start) (bits := 56) (by decide) (by omega)]; omega),
      Pointer.offset_add_nat p (4*start) (bits := 56) (by decide) (by omega),
      Pointer.offset_add_nat p (4*(start+i)) (bits := 56) (by decide) nowrap]
    omega

/-- Contents after reversing exactly one slice. -/
def reverseSlice (xs : Values) (start len : Nat) : Values := fun j ↦
  if start ≤ j ∧ j < start+len then xs (start + (len-1-(j-start))) else xs j

theorem wordsAt_slice (m : Memory) (p : BitVec 64) (n start len : Nat) (xs : Values)
    (mem : WordsAt m p n xs) (inside : start+len ≤ n)
    (nowrap : Pointer.offset 56 p + 4*n < 2^56) :
    WordsAt m (address p start) len (fun j ↦ xs (start+j)) := by
  intro j hj
  rw [address_slice p start j (by omega)]
  exact mem (start+j) (by omega)

/-- Compose a slice contract with the complete array and its surrounding byte frame. -/
theorem reverse_slice (before after : Memory) (p : BitVec 64) (n start len : Nat) (xs : Values)
    (mem : WordsAt before p n xs) (inside : start+len ≤ n)
    (nowrap : Pointer.offset 56 p + 4*n < 2^56)
    (reversed : Reverse.Reversed before after (address p start) len (fun j ↦ xs (start+j))) :
    WordsAt after p n (reverseSlice xs start len) ∧ Frame before after p n := by
  have obj (j : Nat) : Pointer.object 56 (address p j) = Pointer.object 56 p :=
    Pointer.object_add p _
  have off (j : Nat) (hj : j ≤ n) :
      Pointer.offset 56 (address p j) = Pointer.offset 56 p + 4*j :=
    Pointer.offset_add_nat p (4*j) (by decide) (by omega)
  constructor
  · intro j hj
    by_cases within : start ≤ j ∧ j < start+len
    · have h := reversed.1 (j-start) (by omega)
      rw [address_slice p start (j-start) (by omega), show start+(j-start) = j by omega] at h
      simpa [reverseSlice, within] using h
    · simp only [reverseSlice, within, ↓reduceIte]
      apply valueAt_of_bytes before after _ _ (mem j hj)
      intro k hk
      apply reversed.2
      simp only [obj, off j (by omega), off start (by omega)]
      omega
  · intro object offset outside
    apply reversed.2
    simp only [obj, off start (by omega)]
    rcases outside with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl (by omega))
    · exact Or.inr (Or.inr (by omega))

theorem frame_trans (a b c : Memory) (p : BitVec 64) (n : Nat)
    (first : Frame a b p n) (second : Frame b c p n) : Frame a c p n := by
  intro object offset outside
  rw [second object offset outside, first object offset outside]

end ArrayExamples

namespace ArrayExamples
open GotoLean
@[simp] theorem address_zero (p : BitVec 64) : address p 0 = p :=
  Pointer.add_zero p (by decide)
end ArrayExamples
