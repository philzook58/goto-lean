import Generated.Reverse
import GotoLean.Paths
import Proofs.Array

namespace ArrayExamples.Reverse
open GotoLean

private def swapped (m : Memory) (p q : BitVec 64) (x y : BitVec 32) :=
  (m.written 56 p y).written 56 q x

private def view (xs : Values) (n i : Nat) : Values := fun j ↦
  if j < i ∨ n - i ≤ j then xs (n - 1 - j) else xs j

private theorem swap_view (xs : Values) (n i : Nat) (hi : i < n/2) (j : Nat) (hj : j < n) :
    (if j = n-1-i then view xs n i i else
      if j = i then view xs n i (n-1-i) else view xs n i j) = view xs n (i+1) j := by
  unfold view
  grind

private theorem view_finished (xs : Values) (n j : Nat) (hj : j < n) :
    view xs n (n/2) j = xs (n-1-j) := by
  unfold view
  split
  · rfl
  · congr 1; omega

private theorem swapped_view (p : BitVec 64) (n i : Nat) (xs : Values) (m : Memory)
    (mem : WordsAt m p n (view xs n i)) (hi : i < n/2)
    (nowrap : Pointer.offset 56 p + 4*n < 2^56) :
    WordsAt (swapped m (address p i) (address p (n-1-i))
      (view xs n i i) (view xs n i (n-1-i))) p n (view xs n (i+1)) := by
  have hleft : i < n := by omega
  have hright : n-1-i < n := by omega
  have first := wordsAt_written m p n _ mem nowrap i hleft (view xs n i (n-1-i))
  have second := wordsAt_written _ p n _ first nowrap (n-1-i) hright (view xs n i i)
  intro j hj
  simpa only [swapped, swap_view xs n i hi j hj] using second j hj

private theorem swapped_frame (p : BitVec 64) (n i : Nat) (xs : Values)
    (before m : Memory) (mem : WordsAt m p n (view xs n i))
    (frame : Frame before m p n) (hi : i < n/2)
    (nowrap : Pointer.offset 56 p + 4*n < 2^56) :
    Frame before (swapped m (address p i) (address p (n-1-i))
      (view xs n i i) (view xs n i (n-1-i))) p n := by
  have hleft : i < n := by omega
  have hright : n-1-i < n := by omega
  have first := wordsAt_written m p n _ mem nowrap i hleft (view xs n i (n-1-i))
  exact frame_written before _ p n
    (frame_written before m p n frame i hleft nowrap _ (mem i hleft).1)
    (n-1-i) hright nowrap _ (first (n-1-i) hright).1

/-- The ACSL reverse and assigns clauses, expressed over the original executable memory. -/
def Reversed (before after : Memory) (p : BitVec 64) (n : Nat) (xs : Values) : Prop :=
  WordsAt after p n (fun j ↦ xs (n-1-j)) ∧ Frame before after p n

private def cut (f : v_reverse.Frame) : Bool :=
  match f with
  | (.v_reverse (.b4, _), []) => true
  | _ => false

private def state (s : v_reverse.Functions.v_reverse.Locals) : v_reverse.Frame :=
  (.v_reverse (.b4, s), [])

private theorem loop (p : BitVec 64) (n : BitVec 32) (before : Memory) (xs : Values)
    (nowrap : Pointer.offset 56 p + 4*n.toNat < 2^56) (Q : v_reverse.Output → Prop)
    (post : ∀ after, Reversed before after p n.toNat xs → Q ((), after))
    (s : v_reverse.Functions.v_reverse.Locals)
    (ha : s.v_a = p) (hn : s.v_n = n) (half : s.v_half = n/2)
    (bound : s.v_i.toNat ≤ n.toNat/2)
    (mem : WordsAt s.memory p n.toNat (view xs n.toNat s.v_i.toNat))
    (frame : Frame before s.memory p n.toNat) :
    finishes v_reverse.step (4*(n.toNat/2-s.v_i.toNat)+2) (state s) Q := by
  induction gap : n.toNat/2-s.v_i.toNat using Nat.strongRecOn generalizing s with
  | ind remaining ih =>
    by_cases lt : s.v_i.toNat < n.toNat/2
    · have left : s.v_i.toNat < n.toNat := by omega
      have right : n.toNat-1-s.v_i.toNat < n.toNat := by omega
      have sub : ((s.v_n-1)-s.v_i).toNat = n.toNat-1-s.v_i.toNat := by
        have first : (n-1).toNat = n.toNat-1 :=
          BitVec.toNat_sub_of_le (by simp only [BitVec.le_def]; change 1 ≤ n.toNat; omega)
        rw [hn, BitVec.toNat_sub_of_le (by
          simp only [BitVec.le_def, first]; omega), first]
      have inc : (s.v_i+1).toNat = s.v_i.toNat+1 := by
        apply BitVec.toNat_add_of_lt
        have := n.isLt
        change s.v_i.toNat+1 < 2^32
        omega
      let p1 := address p s.v_i.toNat
      let p2 := address p (n.toNat-1-s.v_i.toNat)
      let x := view xs n.toNat s.v_i.toNat s.v_i.toNat
      let y := view xs n.toNat s.v_i.toNat (n.toNat-1-s.v_i.toNat)
      let after := swapped s.memory p1 p2 x y
      have hp : s.memory.ValueAt 56 p1 x := mem _ left
      have hq : s.memory.ValueAt 56 p2 y := mem _ right
      have qvalid : (s.memory.written 56 p1 y).valid 56 p2 4 = true := by
        rw [Memory.valid_of_extent s.memory _ (Memory.written_extent s.memory 56 p1 y hp.1)]
        exact hq.1
      have next := ih (remaining-1) (by omega) { s with v_i := s.v_i+1, memory := after }
        ha hn half (by dsimp only; rw [inc]; omega)
        (by simpa only [inc] using swapped_view p n.toNat s.v_i.toNat xs s.memory mem lt nowrap)
        (swapped_frame p n.toNat s.v_i.toNat xs before s.memory mem frame lt nowrap)
        (by dsimp only; rw [inc]; omega)
      rw [show 4*remaining+2 = 4+(4*(remaining-1)+2) by omega]
      apply path_finishes v_reverse.step cut 4 (4*(remaining-1)+2)
      have test : BitVec.ult s.v_i s.v_half = true := by
        simpa [BitVec.ult, half, BitVec.toNat_udiv] using lt
      simp only [path, v_reverse.step, callStep, v_reverse.body, v_rotate.body, state, cut, test,
        Bool.not_true, Bool.false_eq_true, ↓reduceIte, Bind.bind, Action.wp_bind,
        Action.wp_pure, Sum.elim, ha, index_address, sub, v_rotate.Functions.v_swap.initial,
        choose, Action.wp]
      intro choice
      rw [Memory.load_value _ _ _ _ _ hp, Memory.load_value _ _ _ _ _ hq, Memory.store_wp]
      refine ⟨hp.1, qvalid, ?_⟩
      simpa [state, after, swapped, p1, p2, Memory.written, ha,
        v_reverse.step, v_reverse.offsetBits,
        Bind.bind, Action.wp_bind, Action.wp_pure, Action.wp] using next
    · have eq : s.v_i.toNat = n.toNat/2 := by omega
      have test : BitVec.ult s.v_i s.v_half = false := by
        simp [BitVec.ult, half, BitVec.toNat_udiv, eq]
      have zero : remaining = 0 := by omega
      subst remaining
      simp only [finishes, v_reverse.step, callStep, v_reverse.body, v_rotate.body, state, test,
        Bool.not_false, ↓reduceIte, Bind.bind, Action.wp_bind, Action.wp_pure,
        Sum.elim, v_reverse.finish]
      apply post s.memory
      refine ⟨?_, frame⟩
      intro j hj
      simpa only [eq, view_finished xs n.toNat j hj] using mem j hj

private theorem completed (p : BitVec 64) (n : BitVec 32) (m : Memory) (xs : Values)
    (mem : WordsAt m p n.toNat xs) (nowrap : Pointer.offset 56 p + 4*n.toNat < 2^56)
    (Q : v_reverse.Output → Prop) (post : ∀ after, Reversed m after p n.toNat xs → Q ((), after)) :
    finishes v_reverse.step (4*(n.toNat/2)+3) (v_reverse.initial p n m) Q := by
  have rest := loop p n m xs nowrap Q post
    { v_a := p, v_n := n, v_half := n/2, v_i := 0, memory := m }
    rfl rfl rfl (by simp) (by
      intro j hj
      simpa [view, show ¬ n.toNat ≤ j by omega] using mem j hj) (frame_refl m p n.toNat)
  simp at rest
  unfold finishes
  simpa [v_reverse.initial, v_reverse.Functions.v_reverse.initial,
    v_rotate.Functions.v_reverse.initial,
    v_reverse.step, callStep, v_reverse.body, v_rotate.body, state, Bind.bind, Action.wp_bind,
    choose, Action.wp, divide, show ((2 : BitVec 32) == 0) = false by decide,
    Bool.false_eq_true, ↓reduceIte, Action.wp_pure, Sum.elim, forall_const] using rest

/-- A reusable contract for entering this function in the shared program body. -/
theorem verify (p : BitVec 64) (n : BitVec 32) (m : Memory) (xs : Values)
    (mem : WordsAt m p n.toNat xs) (nowrap : Pointer.offset 56 p + 4*n.toNat < 2^56) :
    finishes v_reverse.step (4*(n.toNat/2)+3) (v_reverse.initial p n m)
      (fun (_, after) ↦ Reversed m after p n.toNat xs) :=
  completed p n m xs mem nowrap _ (fun _ h ↦ h)

/-- Every element is reversed, and every byte outside the array is preserved. -/
theorem correct (p : BitVec 64) (n : BitVec 32) (m : Memory) (xs : Values)
    (mem : WordsAt m p n.toNat xs)
    (nowrap : Pointer.offset 56 p + 4*n.toNat < 2^56) :
    (v_reverse.run p n m).wp (fun (_, after) ↦ Reversed m after p n.toNat xs) :=
  finishes_run _ _ _ _ (completed p n m xs mem nowrap _ (fun _ h ↦ h))

/-- The original call-stack program terminates, including each generated swap call. -/
theorem terminates (p : BitVec 64) (n : BitVec 32) (m : Memory) (xs : Values)
    (mem : WordsAt m p n.toNat xs)
    (nowrap : Pointer.offset 56 p + 4*n.toNat < 2^56) :
    finishes v_reverse.step (4*(n.toNat/2)+3) (v_reverse.initial p n m) (fun _ ↦ True) :=
  completed p n m xs mem nowrap _ (fun _ _ ↦ trivial)

end ArrayExamples.Reverse
