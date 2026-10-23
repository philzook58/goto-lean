import Generated.Rotate
import Proofs.Slices
import GotoLean.CallSummary

namespace ArrayExamples.Rotate
open GotoLean

private def cost (n : BitVec 32) := 4*n.toNat+3

def rotated (xs : Values) (n k : Nat) : Values :=
  fun j ↦ if j < n-k then xs (j+k) else xs (j-(n-k))

private theorem three_reversals (xs : Values) (n k j : Nat) (bound : k ≤ n) (hj : j < n) :
    reverseSlice (reverseSlice (reverseSlice xs 0 k) k (n-k)) 0 n j = rotated xs n k j := by
  unfold reverseSlice rotated
  grind

private theorem call_slice (p q : BitVec 64) (n : BitVec 32) (start : Nat) (len : BitVec 32)
    (m : Memory) (xs : Values) (located : address p start = q) (inside : start+len.toNat ≤ n.toNat)
    (mem : WordsAt m p n.toNat xs) (nowrap : Pointer.offset 56 p+4*n.toNat < 2^56)
    (resume : v_rotate.Value → Action v_rotate.Activation) (tail : Nat)
    (Q : v_rotate.Output → Prop)
    (returns : ∀ after, WordsAt after p n.toNat (reverseSlice xs start len.toNat) →
      Frame m after p n.toNat → (resume (.v_reverse ((), after))).wp
        (fun frame ↦ finishes v_rotate.step tail (frame, []) Q)) :
    finishes v_rotate.step (cost n+tail)
      (.v_reverse (v_rotate.Functions.v_reverse.initial q len m), [resume]) Q := by
  have submem := wordsAt_slice m p n.toNat start len.toNat xs mem inside nowrap
  have subnow : Pointer.offset 56 (address p start)+4*len.toNat < 2^56 := by
    rw [address, Pointer.offset_add_nat p (4*start) (bits := 56) (by decide) (by omega)]
    omega
  rw [located] at submem subnow
  have verified := Reverse.verify q len m (fun j ↦ xs (start+j)) submem subnow
  have bounded := finishes_mono v_reverse.step
    (show 4*(len.toNat/2)+3 ≤ cost n by unfold cost; omega) _ _ verified
  apply finishes_resume v_rotate.body v_reverse.finish v_rotate.finish resume [] tail
    (fun (_, after) ↦ Reverse.Reversed m after q len.toNat
      (fun j ↦ xs (start+j))) Q ?_ (cost n) _ [] bounded
  intro value valid
  cases value with
  | v_reverse output =>
    rcases output with ⟨u, after⟩
    cases u
    change Reverse.Reversed m after q len.toNat (fun j ↦ xs (start+j)) at valid
    rw [← located] at valid
    obtain ⟨words, frame⟩ := reverse_slice m after p n.toNat start len.toNat xs
      mem inside nowrap valid
    exact returns after words frame
  | v_rotate output => simp [v_reverse.finish, Action.wp] at valid
  | v_swap output => simp [v_reverse.finish, Action.wp] at valid

private def frameAt (p : BitVec 64) (k n : BitVec 32) (pc : v_rotate.Functions.v_rotate.PC)
    (m : Memory) : v_rotate.Frame :=
  (.v_rotate (pc, { v_a := p, v_p := k, v_n := n, memory := m }), [])

def Rotated (before : Memory) (p : BitVec 64) (k n : BitVec 32) (xs : Values)
    (out : v_rotate.Output) : Prop :=
  out.1 = n-k ∧ WordsAt out.2 p n.toNat (rotated xs n.toNat k.toNat) ∧
    Frame before out.2 p n.toNat

private theorem exit (before m : Memory) (p : BitVec 64) (k n : BitVec 32) (xs : Values)
    (mem : WordsAt m p n.toNat (rotated xs n.toNat k.toNat))
    (frame : Frame before m p n.toNat) :
    finishes v_rotate.step 2 (frameAt p k n .b4 m) (Rotated before p k n xs) := by
  simpa [finishes, frameAt, v_rotate.step, callStep, v_rotate.body, v_rotate.finish,
    Bind.bind, Action.wp_bind, Action.wp_pure, Rotated] using And.intro mem frame

private theorem last_call (before m : Memory) (p : BitVec 64) (k n : BitVec 32) (xs : Values)
    (bound : k.toNat ≤ n.toNat) (nowrap : Pointer.offset 56 p+4*n.toNat < 2^56)
    (mem : WordsAt m p n.toNat
      (reverseSlice (reverseSlice xs 0 k.toNat) k.toNat (n.toNat-k.toNat)))
    (frame : Frame before m p n.toNat) :
    finishes v_rotate.step (cost n+3) (frameAt p k n .b3 m) (Rotated before p k n xs) := by
  unfold finishes
  simp only [frameAt, v_rotate.step, callStep, v_rotate.body, Bind.bind,
    Action.wp_bind, Action.wp_pure, Sum.elim]
  apply call_slice p p n 0 n m _ (address_zero p) (by omega) mem nowrap
  intro after words changed
  apply exit before after p k n xs ?_ (frame_trans before m after p n.toNat frame changed)
  intro j hj
  simpa only [three_reversals xs n.toNat k.toNat j bound hj] using words j hj

private theorem middle_call (before m : Memory) (p : BitVec 64) (k n : BitVec 32) (xs : Values)
    (bound : k.toNat ≤ n.toNat) (nowrap : Pointer.offset 56 p+4*n.toNat < 2^56)
    (mem : WordsAt m p n.toNat (reverseSlice xs 0 k.toNat)) (frame : Frame before m p n.toNat) :
    finishes v_rotate.step (2*cost n+4) (frameAt p k n .b2 m) (Rotated before p k n xs) := by
  have sub : (n-k).toNat = n.toNat-k.toNat :=
    BitVec.toNat_sub_of_le (by simpa only [BitVec.le_def] using bound)
  rw [show 2*cost n+4 = (cost n+(cost n+3))+1 by omega]
  unfold finishes
  simp only [frameAt, v_rotate.step, callStep, v_rotate.body, Bind.bind,
    Action.wp_bind, Action.wp_pure, Sum.elim, index_address]
  apply call_slice p (address p k.toNat) n k.toNat (n-k) m _ rfl (by rw [sub]; omega) mem nowrap
  intro after words changed
  apply last_call before after p k n xs bound nowrap ?_
    (frame_trans before m after p n.toNat frame changed)
  simpa only [sub] using words

private theorem first_call (p : BitVec 64) (k n : BitVec 32) (m : Memory) (xs : Values)
    (bound : k.toNat ≤ n.toNat) (nowrap : Pointer.offset 56 p+4*n.toNat < 2^56)
    (mem : WordsAt m p n.toNat xs) :
    finishes v_rotate.step (3*cost n+5) (frameAt p k n .b1 m) (Rotated m p k n xs) := by
  rw [show 3*cost n+5 = (cost n+(2*cost n+4))+1 by omega]
  unfold finishes
  simp only [frameAt, v_rotate.step, callStep, v_rotate.body, Bind.bind,
    Action.wp_bind, Action.wp_pure, Sum.elim]
  apply call_slice p p n 0 k m xs (address_zero p) (by omega) mem nowrap
  intro after words changed
  exact middle_call m after p k n xs bound nowrap words changed

/-- The original three-call rotation is safe, terminates, and rotates every element.
The result is `n-k`, and every byte outside the array is unchanged. -/
theorem verify (p : BitVec 64) (k n : BitVec 32) (m : Memory) (xs : Values)
    (bound : k.toNat ≤ n.toNat) (mem : WordsAt m p n.toNat xs)
    (nowrap : Pointer.offset 56 p+4*n.toNat < 2^56) :
    finishes v_rotate.step (12*n.toNat+15) (v_rotate.initial p k n m) (Rotated m p k n xs) := by
  rw [show 12*n.toNat+15 = 3*cost n+6 by unfold cost; omega]
  unfold finishes
  simp only [v_rotate.initial, v_rotate.Functions.v_rotate.initial, v_rotate.step, callStep,
    v_rotate.body, Bind.bind, Action.wp_bind]
  split
  all_goals simp only [Action.wp_pure, Sum.elim]
  · rename_i skip
    have edge : k.toNat = 0 ∨ k.toNat = n.toNat := by
      have h : k.toNat = 0 ∨ n.toNat ≤ k.toNat := by simpa [BitVec.ult] using skip
      omega
    apply finishes_mono v_rotate.step (show 2 ≤ 3*cost n+5 by unfold cost; omega)
    apply exit m m p k n xs ?_ (frame_refl m p n.toNat)
    intro j hj
    have eq : rotated xs n.toNat k.toNat j = xs j := by
      rcases edge with zero | full
      · simp [rotated, zero, hj]
      · simp [rotated, full]
    simpa only [eq] using mem j hj
  · change finishes v_rotate.step (3*cost n+5) (frameAt p k n .b1 m) _
    exact first_call p k n m xs bound nowrap mem

end ArrayExamples.Rotate
