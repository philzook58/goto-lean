import Generated.IsSortedUntil
import GotoLean.Paths
import Proofs.Array

namespace ArrayExamples.IsSortedUntil
open GotoLean

/-- Exactly the ACSL maximal sorted-prefix contract. -/
def Prefix (xs : Values) (n r : Nat) : Prop :=
  r ≤ n ∧ Increasing xs r ∧ (r < n → ¬ Increasing xs (r+1))

private theorem extend (xs : Values) (k : Nat) (hk : 0 < k) (sorted : Increasing xs k)
    (last : (xs (k-1)).toInt ≤ (xs k).toInt) : Increasing xs (k+1) := by
  intro i j hij hj
  by_cases old : j < k
  · exact sorted i j hij old
  · have eq : j = k := by omega
    subst j
    by_cases same : i = k
    · simp [same]
    · have := sorted i (k-1) (by omega) (by omega); omega

private def cut (f : v_is_sorted_until.Frame) := match f.1 with | .b2 => true | _ => false
private def invariant (p : BitVec 64) (n : BitVec 32) (m : Memory) (xs : Values)
    (f : v_is_sorted_until.Frame) : Prop :=
  let s := f.2
  s.v_a = p ∧ s.v_n = n ∧ s.memory = m ∧
  match f.1 with
  | .b0 => True
  | .b2 => 1 ≤ s.v_i.toNat ∧ s.v_i.toNat ≤ max 1 n.toNat ∧ Increasing xs s.v_i.toNat
  | _ => False
private def rank (f : v_is_sorted_until.Frame) :=
  match f.1 with | .b0 => f.2.v_n.toNat+1 | _ => f.2.v_n.toNat-f.2.v_i.toNat

private theorem segments (p : BitVec 64) (n : BitVec 32) (m : Memory) (xs : Values)
    (mem : WordsAt m p n.toNat xs) (f : v_is_sorted_until.Frame)
    (hi : invariant p n m xs f) :
    (path v_is_sorted_until.step cut 4 f).wp
      (Sum.elim (fun next ↦ invariant p n m xs next ∧ rank next < rank f)
        (fun (r, m') ↦ Prefix xs n.toNat r.toNat ∧ m' = m)) := by
  rcases f with ⟨pc, s⟩
  obtain ⟨ha, hn, hm, hi⟩ := hi
  dsimp only at ha hn hm
  cases pc <;> dsimp only at hi
  all_goals try exact hi.elim
  case b0 =>
    simp [path, cut, v_is_sorted_until.step, Bind.bind, Action.wp_bind, choose, Action.wp,
      invariant, rank, ha, hn, hm]
    refine ⟨⟨by omega, ?_⟩, by omega⟩
    intro i j hij hj
    have eq : i = j := by omega
    simp [eq]
  case b2 =>
    obtain ⟨positive, bound, sorted⟩ := hi
    unfold path
    simp only [v_is_sorted_until.step, Bind.bind, Action.wp_bind]
    split
    · rename_i stop
      have ge : n.toNat ≤ s.v_i.toNat := by simpa [BitVec.ult, hn] using stop
      simp only [path, cut, v_is_sorted_until.step, Bind.bind, Action.wp_bind, Action.wp_pure,
        Bool.false_eq_true, ↓reduceIte, Sum.elim, hn]
      refine ⟨⟨by omega, ?_, by omega⟩, hm⟩
      intro i j hij hj
      exact sorted i j hij (by omega)
    · rename_i continuing
      have lt : s.v_i.toNat < n.toNat := by simpa [BitVec.ult, hn] using continuing
      have sub := index_predecessor s.v_i positive
      have prev := mem (s.v_i.toNat-1) (by omega)
      have current := mem s.v_i.toNat lt
      have inc := index_increment s.v_i n lt
      simp only [cut, path, v_is_sorted_until.step, Bind.bind, Action.wp_bind, Action.wp_pure,
        Bool.false_eq_true, ↓reduceIte]
      rw [ha, hm, index_address, sub, Memory.load_value _ _ _ _ _ prev,
        index_address, Memory.load_value _ _ _ _ _ current]
      split <;> simp_all only [Action.wp_bind,
        Action.wp_pure, Sum.elim, invariant, rank, Bool.false_eq_true, ↓reduceIte, BitVec.slt]
      · have next := extend xs s.v_i.toNat (by omega) sorted (by simp_all)
        simp only [true_and]
        exact ⟨⟨by omega, by omega, next⟩, by omega⟩
      · simp only [Prefix]
        refine ⟨⟨by omega, sorted, ?_⟩, trivial⟩
        intro _ impossible
        have := impossible (s.v_i.toNat-1) s.v_i.toNat (by omega) (by omega)
        simp_all

/-- Every input has a maximal sorted prefix; all reads are safe and memory is unchanged. -/
theorem verify (p : BitVec 64) (n : BitVec 32) (m : Memory) (xs : Values)
    (mem : WordsAt m p n.toNat xs) :
    finishes v_is_sorted_until.step (4*(n.toNat+2)) (v_is_sorted_until.initial p n m)
      (fun (r, m') ↦ Prefix xs n.toNat r.toNat ∧ m' = m) := by
  apply finishes_paths v_is_sorted_until.step cut 4 (n.toNat+2)
  exact finishes_of_rank _ (invariant p n m xs) rank _ (segments p n m xs mem)
    _ ⟨rfl, rfl, rfl, trivial⟩

end ArrayExamples.IsSortedUntil
