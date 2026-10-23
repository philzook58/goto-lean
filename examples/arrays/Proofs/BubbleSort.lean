import Generated.BubbleSort
import GotoLean.Paths
import Proofs.Array
import Init.Data.Array.Perm

namespace ArrayExamples.BubbleSort
open GotoLean

/-- The complete array contents, including repeated values. -/
def elements (xs : Values) (n : Nat) : Array (BitVec 32) :=
  Array.ofFn (fun i : Fin n ↦ xs i)

private def exchange (xs : Values) (i j : Nat) : Values :=
  fun k ↦ if k = j then xs i else if k = i then xs j else xs k

private theorem exchange_perm (xs : Values) (n i j : Nat) (hi : i < n) (hj : j < n) :
    (elements (exchange xs i j) n).Perm (elements xs n) := by
  have hai : i < (elements xs n).size := by simpa [elements] using hi
  have haj : j < (elements xs n).size := by simpa [elements] using hj
  have eq : elements (exchange xs i j) n = (elements xs n).swap i j hai haj := by
    apply Array.ext
    · simp [elements]
    · intro k hk hl
      simp only [elements, exchange, Array.getElem_swap, Array.getElem_ofFn]
      grind
  rw [eq]
  exact Array.swap_perm (by simpa [elements] using hi) (by simpa [elements] using hj)

/-- Every element is ordered against the sorted suffix starting at `k`. -/
private def Suffix (xs : Values) (n k : Nat) : Prop :=
  ∀ a b, a ≤ b → b < n → k ≤ b → (xs a).toInt ≤ (xs b).toInt

private def Maximum (xs : Values) (j : Nat) : Prop :=
  ∀ a, a ≤ j → (xs a).toInt ≤ (xs j).toInt

private theorem suffix_empty (xs : Values) (n : Nat) : Suffix xs n n := by
  intro a b hab hb hk
  omega

private theorem suffix_sorted (xs : Values) (n : Nat) (h : Suffix xs n 1) :
    Increasing xs n := by
  intro a b hab hb
  by_cases zero : b = 0
  · have eq : a = b := by omega
    simp [eq]
  · exact h a b hab hb (by omega)

private theorem suffix_extend (xs : Values) (n k : Nat) (h : Suffix xs n (k+1))
    (maximum : Maximum xs k) : Suffix xs n k := by
  intro a b hab hb hk
  by_cases eq : b = k
  · simpa [eq] using maximum a (by omega)
  · exact h a b hab hb (by omega)

private theorem suffix_exchange (xs : Values) (n k i j : Nat)
    (h : Suffix xs n k) (hi : i < k) (hj : j < k) :
    Suffix (exchange xs i j) n k := by
  intro a b hab hb hk
  have bi : b ≠ i := by omega
  have bj : b ≠ j := by omega
  simp only [exchange, bi, bj, ↓reduceIte]
  split
  · exact h i b (by omega) hb hk
  · split
    · exact h j b (by omega) hb hk
    · exact h a b hab hb hk

private theorem maximum_ordered (xs : Values) (j : Nat) (h : Maximum xs j)
    (ordered : (xs j).toInt ≤ (xs (j+1)).toInt) : Maximum xs (j+1) := by
  intro a ha
  by_cases eq : a = j+1
  · simp [eq]
  · exact Int.le_trans (h a (by omega)) ordered

private theorem maximum_exchange (xs : Values) (j : Nat) (h : Maximum xs j)
    (outOfOrder : (xs (j+1)).toInt < (xs j).toInt) :
    Maximum (exchange xs j (j+1)) (j+1) := by
  intro a ha
  simp only [exchange, ↓reduceIte]
  split
  · omega
  · split
    · omega
    · exact h a (by omega)

private def swapped (m : Memory) (p : BitVec 64) (xs : Values) (j : Nat) : Memory :=
  (m.written 56 (address p j) (xs (j+1))).written 56 (address p (j+1)) (xs j)

private theorem swap_contents (m : Memory) (p : BitVec 64) (n j : Nat) (xs : Values)
    (mem : WordsAt m p n xs) (hj : j+1 < n)
    (nowrap : Pointer.offset 56 p+4*n < 2^56) :
    WordsAt (swapped m p xs j) p n (exchange xs j (j+1)) := by
  have first := wordsAt_written m p n xs mem nowrap j (by omega) (xs (j+1))
  have second := wordsAt_written _ p n _ first nowrap (j+1) hj (xs j)
  exact second

private theorem swap_frame (before m : Memory) (p : BitVec 64) (n j : Nat) (xs : Values)
    (mem : WordsAt m p n xs) (frame : Frame before m p n) (hj : j+1 < n)
    (nowrap : Pointer.offset 56 p+4*n < 2^56) : Frame before (swapped m p xs j) p n := by
  have first := wordsAt_written m p n xs mem nowrap j (by omega) (xs (j+1))
  exact frame_written before _ p n
    (frame_written before m p n frame j (by omega) nowrap _ (mem j (by omega)).1)
    (j+1) hj nowrap _ (first (j+1) hj).1

/-- Signed sortedness, a permutation of every original element, and the surrounding byte frame. -/
def Sorted (before after : Memory) (p : BitVec 64) (n : Nat) (xs : Values) : Prop :=
  ∃ ys, WordsAt after p n ys ∧ Increasing ys n ∧
    (elements ys n).Perm (elements xs n) ∧ Frame before after p n

private def cut (f : v_bubble_sort.Frame) : Bool :=
  match f with
  | (.v_bubble_sort (.b3, _), []) | (.v_bubble_sort (.b6, _), []) => true
  | _ => false

private def state (pc : v_bubble_sort.Functions.v_bubble_sort.PC)
    (s : v_bubble_sort.Functions.v_bubble_sort.Locals) : v_bubble_sort.Frame :=
  (.v_bubble_sort (pc, s), [])

private def invariant (p : BitVec 64) (n : BitVec 32) (before : Memory) (xs : Values)
    (f : v_bubble_sort.Frame) : Prop :=
  match f with
  | (.v_bubble_sort (pc, s), []) =>
    s.v_a = p ∧ s.v_n = n ∧ ∃ ys, WordsAt s.memory p n.toNat ys ∧
      (elements ys n.toNat).Perm (elements xs n.toNat) ∧ Frame before s.memory p n.toNat ∧
      match pc with
      | .b0 => True
      | .b3 => 1 ≤ s.v_i.toNat ∧ s.v_i.toNat ≤ n.toNat ∧
          Suffix ys n.toNat (n.toNat-s.v_i.toNat+1)
      | .b6 => 1 ≤ s.v_i.toNat ∧ s.v_i.toNat < n.toNat ∧
          s.v_j.toNat ≤ n.toNat-s.v_i.toNat ∧
          Suffix ys n.toNat (n.toNat-s.v_i.toNat+1) ∧ Maximum ys s.v_j.toNat
      | _ => False
  | _ => False

private def rank (n : BitVec 32) (f : v_bubble_sort.Frame) : Nat :=
  match f with
  | (.v_bubble_sort (.b3, s), []) => (n.toNat-s.v_i.toNat+1)*(n.toNat+2)
  | (.v_bubble_sort (.b6, s), []) =>
      (n.toNat-s.v_i.toNat)*(n.toNat+2)+(n.toNat-s.v_i.toNat-s.v_j.toNat)+1
  | _ => (n.toNat+1)*(n.toNat+2)+1

private theorem entry (p : BitVec 64) (n : BitVec 32) (before : Memory) (xs ys : Values)
    (s : v_bubble_sort.Functions.v_bubble_sort.Locals) (ha : s.v_a = p) (hn : s.v_n = n)
    (mem : WordsAt s.memory p n.toNat ys)
    (perm : (elements ys n.toNat).Perm (elements xs n.toNat))
    (frame : Frame before s.memory p n.toNat) :
    (path v_bubble_sort.step cut 5 (state .b0 s)).wp
      (Sum.elim (fun next ↦ invariant p n before xs next ∧ rank n next < rank n (state .b0 s))
        (fun (_, after) ↦ Sorted before after p n.toNat xs)) := by
  by_cases zero : n.toNat = 0
  · have test : BitVec.ult (0 : BitVec 32) s.v_n = false := by simp [BitVec.ult, hn, zero]
    simp only [path, state, v_bubble_sort.step, callStep, v_bubble_sort.body, test,
      Bool.not_false, ↓reduceIte, cut, Bind.bind, Action.wp_bind, Action.wp_pure,
      v_bubble_sort.finish]
    refine ⟨ys, mem, ?_, perm, frame⟩
    intro a b hab hb
    omega
  · have test : BitVec.ult (0 : BitVec 32) s.v_n = true := by
      simp [BitVec.ult, hn]; omega
    simp only [path, state, v_bubble_sort.step, callStep, v_bubble_sort.body, test,
      Bool.not_true, Bool.false_eq_true, ↓reduceIte, cut, Bind.bind, Action.wp_bind,
      Action.wp_pure, Sum.elim, choose, Action.wp]
    intro choice
    refine ⟨⟨ha, hn, ys, mem, perm, frame, ?_, ?_, ?_⟩, ?_⟩
    · simp
    · simp; omega
    · simpa only [show (1 : BitVec 32).toNat = 1 from rfl,
        show n.toNat-1+1 = n.toNat by omega] using suffix_empty ys n.toNat
    · change (n.toNat-1+1)*(n.toNat+2) < (n.toNat+1)*(n.toNat+2)+1
      rw [show n.toNat-1+1 = n.toNat by omega, Nat.add_mul, Nat.one_mul]
      omega

private theorem outer (p : BitVec 64) (n : BitVec 32) (before : Memory) (xs ys : Values)
    (s : v_bubble_sort.Functions.v_bubble_sort.Locals) (ha : s.v_a = p) (hn : s.v_n = n)
    (mem : WordsAt s.memory p n.toNat ys)
    (perm : (elements ys n.toNat).Perm (elements xs n.toNat))
    (frame : Frame before s.memory p n.toNat) (lo : 1 ≤ s.v_i.toNat)
    (hi : s.v_i.toNat ≤ n.toNat) (suffix : Suffix ys n.toNat (n.toNat-s.v_i.toNat+1)) :
    (path v_bubble_sort.step cut 5 (state .b3 s)).wp
      (Sum.elim (fun next ↦ invariant p n before xs next ∧ rank n next < rank n (state .b3 s))
        (fun (_, after) ↦ Sorted before after p n.toNat xs)) := by
  by_cases lt : s.v_i.toNat < n.toNat
  · have test : BitVec.ult s.v_i s.v_n = true := by simpa [BitVec.ult, hn] using lt
    simp only [path, state, v_bubble_sort.step, callStep, v_bubble_sort.body, test,
      Bool.not_true, Bool.false_eq_true, ↓reduceIte, cut, Bind.bind, Action.wp_bind,
      Action.wp_pure, Sum.elim, choose, Action.wp]
    intro choice
    refine ⟨⟨ha, hn, ys, mem, perm, frame, lo, lt, by simp, suffix, ?_⟩, ?_⟩
    · intro a ha
      have eq : a = 0 := by simpa using ha
      simp [eq]
    · simp only [rank, Nat.add_mul, Nat.one_mul]
      omega
  · have eq : s.v_i.toNat = n.toNat := by omega
    have test : BitVec.ult s.v_i s.v_n = false := by simp [BitVec.ult, hn, eq]
    simp only [path, state, v_bubble_sort.step, callStep, v_bubble_sort.body, test,
      Bool.not_false, ↓reduceIte, cut, Bind.bind, Action.wp_bind, Action.wp_pure,
      v_bubble_sort.finish]
    exact ⟨ys, mem, suffix_sorted ys n.toNat (by simpa [eq] using suffix), perm, frame⟩

private theorem inner (p : BitVec 64) (n : BitVec 32) (before : Memory) (xs ys : Values)
    (s : v_bubble_sort.Functions.v_bubble_sort.Locals) (ha : s.v_a = p) (hn : s.v_n = n)
    (mem : WordsAt s.memory p n.toNat ys)
    (perm : (elements ys n.toNat).Perm (elements xs n.toNat))
    (frame : Frame before s.memory p n.toNat) (lo : 1 ≤ s.v_i.toNat)
    (hi : s.v_i.toNat < n.toNat) (bound : s.v_j.toNat ≤ n.toNat-s.v_i.toNat)
    (suffix : Suffix ys n.toNat (n.toNat-s.v_i.toNat+1)) (maximum : Maximum ys s.v_j.toNat)
    (nowrap : Pointer.offset 56 p+4*n.toNat < 2^56) :
    (path v_bubble_sort.step cut 5 (state .b6 s)).wp
      (Sum.elim (fun next ↦ invariant p n before xs next ∧ rank n next < rank n (state .b6 s))
        (fun (_, after) ↦ Sorted before after p n.toNat xs)) := by
  have sub : (s.v_n-s.v_i).toNat = n.toNat-s.v_i.toNat := by
    rw [hn, BitVec.toNat_sub_of_le (by simp only [BitVec.le_def]; omega)]
  by_cases lt : s.v_j.toNat < n.toNat-s.v_i.toNat
  · have test : BitVec.ult s.v_j (s.v_n-s.v_i) = true := by
      simpa [BitVec.ult, sub] using lt
    have hj : s.v_j.toNat+1 < n.toNat := by omega
    have inc := index_increment s.v_j n (by omega)
    have hp := mem s.v_j.toNat (by omega)
    have hq := mem (s.v_j.toNat+1) hj
    simp only [path, state, v_bubble_sort.step, callStep, v_bubble_sort.body, test,
      Bool.not_true, Bool.false_eq_true, ↓reduceIte, cut, Bind.bind, Action.wp_bind,
      Action.wp_pure, ha, index_address, inc]
    rw [Memory.load_value _ _ _ _ _ hp, Memory.load_value _ _ _ _ _ hq]
    by_cases ordered : (ys s.v_j.toNat).toInt ≤ (ys (s.v_j.toNat+1)).toInt
    · have compare : BitVec.slt (ys (s.v_j.toNat+1)) (ys s.v_j.toNat) = false := by
        simpa [BitVec.slt] using (show ¬ (ys (s.v_j.toNat+1)).toInt <
          (ys s.v_j.toNat).toInt by omega)
      simp only [compare, Bool.not_false, ↓reduceIte, Action.wp_pure]
      refine ⟨⟨ha, hn, ys, mem, perm, frame, lo, hi, ?_, suffix, ?_⟩, ?_⟩
      · dsimp only; rw [inc]; omega
      · simpa only [inc] using maximum_ordered ys s.v_j.toNat maximum ordered
      · simp only [rank, inc]
        omega
    · have disorder : (ys (s.v_j.toNat+1)).toInt < (ys s.v_j.toNat).toInt := by omega
      have compare : BitVec.slt (ys (s.v_j.toNat+1)) (ys s.v_j.toNat) = true := by
        simpa [BitVec.slt] using disorder
      have qvalid : (s.memory.written 56 (address p s.v_j.toNat)
          (ys (s.v_j.toNat+1))).valid 56 (address p (s.v_j.toNat+1)) 4 = true := by
        rw [Memory.valid_of_extent s.memory _ (Memory.written_extent s.memory 56 _ _ hp.1)]
        exact hq.1
      simp only [compare, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Action.wp_bind,
        Action.wp_pure, Sum.elim, ha, inc,
        v_bubble_sort.Functions.v_swap.initial, choose, Action.wp]
      intro choice
      rw [Memory.load_value _ _ _ _ _ hp, Memory.load_value _ _ _ _ _ hq]
      simp only [Memory.store_wp]
      refine ⟨hp.1, qvalid, ?_⟩
      refine ⟨⟨rfl, hn, exchange ys s.v_j.toNat (s.v_j.toNat+1),
        swap_contents s.memory p n.toNat s.v_j.toNat ys mem hj nowrap,
        (exchange_perm ys n.toNat s.v_j.toNat (s.v_j.toNat+1) (by omega) hj).trans perm,
        swap_frame before s.memory p n.toNat s.v_j.toNat ys mem frame hj nowrap,
        lo, hi, ?_, ?_, ?_⟩, ?_⟩
      · dsimp only; rw [inc]; omega
      · exact suffix_exchange ys n.toNat (n.toNat-s.v_i.toNat+1)
          s.v_j.toNat (s.v_j.toNat+1) suffix (by omega) (by omega)
      · simpa only [inc] using maximum_exchange ys s.v_j.toNat maximum disorder
      · simp only [rank, inc]
        omega
  · have eq : s.v_j.toNat = n.toNat-s.v_i.toNat := by omega
    have test : BitVec.ult s.v_j (s.v_n-s.v_i) = false := by simp [BitVec.ult, sub, eq]
    have inc := index_increment s.v_i n hi
    simp only [path, state, v_bubble_sort.step, callStep, v_bubble_sort.body, test,
      Bool.not_false, ↓reduceIte, cut, Bind.bind, Action.wp_bind, Action.wp_pure]
    refine ⟨⟨ha, hn, ys, mem, perm, frame, ?_, ?_, ?_⟩, ?_⟩
    · dsimp only; rw [inc]; omega
    · dsimp only; rw [inc]; omega
    · simpa only [inc, show n.toNat-(s.v_i.toNat+1)+1 = n.toNat-s.v_i.toNat by omega]
        using suffix_extend ys n.toNat (n.toNat-s.v_i.toNat) suffix (by simpa [eq] using maximum)
    · simp only [rank, inc, eq, Nat.sub_self]
      rw [show n.toNat-s.v_i.toNat = (n.toNat-(s.v_i.toNat+1))+1 by omega,
        Nat.add_mul, Nat.one_mul]
      omega

private theorem segments (p : BitVec 64) (n : BitVec 32) (before : Memory) (xs : Values)
    (nowrap : Pointer.offset 56 p+4*n.toNat < 2^56)
    (f : v_bubble_sort.Frame) (h : invariant p n before xs f) :
    (path v_bubble_sort.step cut 5 f).wp
      (Sum.elim (fun next ↦ invariant p n before xs next ∧ rank n next < rank n f)
        (fun (_, after) ↦ Sorted before after p n.toNat xs)) := by
  rcases f with ⟨activation, stack⟩
  cases stack with
  | cons k rest => cases activation <;> simp [invariant] at h
  | nil =>
    cases activation with
    | v_swap f => simp [invariant] at h
    | v_bubble_sort f =>
      rcases f with ⟨pc, s⟩
      obtain ⟨ha, hn, ys, mem, perm, frame, h⟩ := h
      cases pc <;> dsimp only at h
      all_goals try exact h.elim
      case b0 => exact entry p n before xs ys s ha hn mem perm frame
      case b3 =>
        obtain ⟨lo, hi, suffix⟩ := h
        exact outer p n before xs ys s ha hn mem perm frame lo hi suffix
      case b6 =>
        obtain ⟨lo, hi, bound, suffix, maximum⟩ := h
        exact inner p n before xs ys s ha hn mem perm frame lo hi bound suffix maximum nowrap

/-- The unchanged nested-loop program sorts signed elements, preserves their permutation and
all surrounding bytes, and completes within a conservative quadratic block bound. -/
theorem verify (p : BitVec 64) (n : BitVec 32) (m : Memory) (xs : Values)
    (mem : WordsAt m p n.toNat xs) (nowrap : Pointer.offset 56 p+4*n.toNat < 2^56) :
    finishes v_bubble_sort.step (5*((n.toNat+1)*(n.toNat+2)+2)) (v_bubble_sort.initial p n m)
      (fun (_, after) ↦ Sorted m after p n.toNat xs) := by
  apply finishes_paths v_bubble_sort.step cut 5 ((n.toNat+1)*(n.toNat+2)+2)
  exact finishes_of_rank _ (invariant p n m xs) (rank n) _ (segments p n m xs nowrap)
    _ ⟨rfl, rfl, xs, mem, .refl _, frame_refl m p n.toNat, trivial⟩

end ArrayExamples.BubbleSort
