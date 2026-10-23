import Generated.Find
import GotoLean.Paths
import Proofs.Array

namespace ArrayExamples.Find
open GotoLean

/-- The first matching index, or `n` when the value is absent. -/
def Found (xs : Values) (n : Nat) (v : BitVec 32) (r : Nat) : Prop :=
  r ≤ n ∧ (∀ j, j < r → xs j ≠ v) ∧ (r < n → xs r = v)

private def cut (f : v_find.Frame) := match f.1 with | .b2 => true | _ => false
private def invariant (p : BitVec 64) (n v : BitVec 32) (m : Memory) (xs : Values)
    (f : v_find.Frame) : Prop :=
  let s := f.2
  s.v_a = p ∧ s.v_n = n ∧ s.v_v = v ∧ s.memory = m ∧
  match f.1 with
  | .b0 => True
  | .b2 => s.v_i.toNat ≤ n.toNat ∧ ∀ j, j < s.v_i.toNat → xs j ≠ v
  | _ => False
private def rank (f : v_find.Frame) :=
  match f.1 with | .b0 => f.2.v_n.toNat+1 | _ => f.2.v_n.toNat-f.2.v_i.toNat

private theorem segments (p : BitVec 64) (n v : BitVec 32) (m : Memory) (xs : Values)
    (mem : WordsAt m p n.toNat xs) (f : v_find.Frame) (hi : invariant p n v m xs f) :
    (path v_find.step cut 4 f).wp
      (Sum.elim (fun next ↦ invariant p n v m xs next ∧ rank next < rank f)
        (fun (r, m') ↦ Found xs n.toNat v r.toNat ∧ m' = m)) := by
  rcases f with ⟨pc, s⟩
  obtain ⟨ha, hn, hv, hm, hi⟩ := hi
  dsimp only at ha hn hv hm
  cases pc <;> dsimp only at hi
  all_goals try exact hi.elim
  case b0 =>
    simp [path, cut, v_find.step, Bind.bind, Action.wp_bind, choose, Action.wp,
      invariant, rank, ha, hn, hv, hm]
  case b2 =>
    obtain ⟨bound, before⟩ := hi
    unfold path
    simp only [v_find.step, Bind.bind, Action.wp_bind]
    split
    · have eq : s.v_i.toNat = n.toNat := by simp_all [BitVec.ult]; omega
      simp only [path, cut, v_find.step, Bind.bind, Action.wp_bind, Action.wp_pure,
        Sum.elim, Bool.false_eq_true, ↓reduceIte]
      simp only [hn]
      exact ⟨⟨by omega, by simpa [eq] using before, by omega⟩, hm⟩
    · rename_i continuing
      have lt : s.v_i.toNat < n.toNat := by simpa [BitVec.ult, hn] using continuing
      have load := mem s.v_i.toNat lt
      have inc := index_increment s.v_i n lt
      simp only [cut, path, v_find.step, Bind.bind, Action.wp_bind, Action.wp_pure,
        Bool.false_eq_true, ↓reduceIte]
      rw [ha, hm, index_address, Memory.load_value _ _ _ _ _ load]
      split <;> simp_all only [Action.wp_bind,
        Action.wp_pure, Sum.elim, invariant, rank, Bool.false_eq_true, ↓reduceIte]
      all_goals simp only [true_and, Found]
      all_goals grind

/-- The original search is safe and terminates, preserving all memory. -/
theorem verify (p : BitVec 64) (n v : BitVec 32) (m : Memory) (xs : Values)
    (mem : WordsAt m p n.toNat xs) :
    finishes v_find.step (4*(n.toNat+2)) (v_find.initial p n v m)
      (fun (r, m') ↦ Found xs n.toNat v r.toNat ∧ m' = m) := by
  apply finishes_paths v_find.step cut 4 (n.toNat+2)
  exact finishes_of_rank _ (invariant p n v m xs) rank _ (segments p n v m xs mem)
    _ ⟨rfl, rfl, rfl, rfl, trivial⟩

end ArrayExamples.Find
