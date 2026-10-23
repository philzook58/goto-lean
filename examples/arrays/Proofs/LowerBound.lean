import Generated.LowerBound
import Proofs.Array
import GotoLean.Paths

namespace ArrayExamples.LowerBound
open GotoLean

private def midpoint (l r : BitVec 32) := l + (r - l) / 2

private theorem midpoint_bounds (l r : BitVec 32) (h : l.toNat < r.toNat) :
    l.toNat ≤ (midpoint l r).toNat ∧ (midpoint l r).toNat < r.toNat := by
  have hr := r.isLt
  have sub := BitVec.toNat_sub_of_le (x := r) (y := l)
    (by simpa only [BitVec.le_def] using Nat.le_of_lt h)
  have div : ((r - l) / 2).toNat = (r.toNat - l.toNat) / 2 := by
    rw [BitVec.toNat_udiv, sub]; rfl
  have add := BitVec.toNat_add_of_lt (x := l) (y := (r - l) / 2) (by rw [div]; omega)
  simp only [midpoint, add, div]
  omega

private theorem increment (i : BitVec 32) (n : BitVec 32) (h : i.toNat < n.toNat) :
    (i + 1).toNat = i.toNat + 1 := by
  have := n.isLt
  exact BitVec.toNat_add_of_lt (by simpa using (show i.toNat + 1 < 2^32 by omega))

-- Only entry and the loop header need annotations. Other PCs are traversed by `path`.
private def segment : Step v_lower_bound.Frame v_lower_bound.Output :=
  path v_lower_bound.step (fun f ↦ match f.1 with | .b4 => true | _ => false) 4

private def invariant (p : BitVec 64) (n v : BitVec 32) (m : Memory) (xs : Values)
    (f : v_lower_bound.Frame) : Prop :=
  let s := f.2
  s.v_a = p ∧ s.v_n = n ∧ s.v_v = v ∧ s.memory = m ∧
  match f.1 with
  | .b0 => True
  | .b4 => Partition xs n.toNat v s.v_left.toNat s.v_right.toNat
  | _ => False

private def rank (f : v_lower_bound.Frame) : Nat :=
  match f.1 with
  | .b0 => f.2.v_n.toNat + 1
  | _ => f.2.v_right.toNat - f.2.v_left.toNat

private theorem segments (p : BitVec 64) (n v : BitVec 32) (m : Memory) (xs : Values)
    (mem : WordsAt m p n.toNat xs) (sorted : Increasing xs n.toNat)
    (f : v_lower_bound.Frame) (hi : invariant p n v m xs f) :
    (segment f).wp (Sum.elim (fun next ↦ invariant p n v m xs next ∧ rank next < rank f)
      (fun (r, m') ↦ Partition xs n.toNat v r.toNat r.toNat ∧ m' = m)) := by
  rcases f with ⟨pc, s⟩
  obtain ⟨ha, hn, hv, hm, hi⟩ := hi
  dsimp only at ha hn hv hm
  cases pc <;> dsimp only at hi
  all_goals try exact hi.elim
  case b0 =>
    simp [segment, path, v_lower_bound.step, Bind.bind, Action.wp_bind, choose, Action.wp,
      invariant, rank, Partition, ha, hn, hv, hm]
    intro i hge hlt; omega
  case b4 =>
    obtain ⟨hlr, hrn, before, after⟩ := hi
    unfold segment path
    simp only [v_lower_bound.step, Bind.bind, Action.wp_bind]
    split
    · simp [path, v_lower_bound.step, Bind.bind, Action.wp_bind, Action.wp_pure,
        invariant, rank, Sum.elim, ha, hn, hv, hm]
      have eq : s.v_left.toNat = s.v_right.toNat := by
        simp_all [BitVec.ult]
        omega
      exact ⟨by omega, by omega, before, by simpa [eq] using after⟩
    · rename_i continuing
      have lt : s.v_left.toNat < s.v_right.toNat := by
        simpa [BitVec.ult] using continuing
      have mid := midpoint_bounds s.v_left s.v_right lt
      have load := mem (midpoint s.v_left s.v_right).toNat (by omega)
      simp only [Action.wp_pure]
      unfold path
      simp only [v_lower_bound.step, Bool.false_eq_true, ↓reduceIte,
        Bind.bind, Action.wp_bind, choose, Action.wp]
      intro choice
      simp only [divide, show ((2 : BitVec 32) == 0) = false by decide,
        Bool.false_eq_true, ↓reduceIte, Action.wp_pure]
      dsimp only [midpoint] at load mid
      rw [ha, hm, index_address, Memory.load_value _ _ _ _ _ load]
      have inc := increment (s.v_left + (s.v_right - s.v_left) / 2) n (by omega)
      split <;> simp_all only [path, v_lower_bound.step, Bind.bind, Action.wp_bind,
        Action.wp_pure, Bool.false_eq_true, ↓reduceIte, Sum.elim, invariant, rank,
        BitVec.slt]
      all_goals simp only [true_and, Partition]
      all_goals grind only [Increasing]

private theorem completed (p : BitVec 64) (n v : BitVec 32) (m : Memory) (xs : Values)
    (mem : WordsAt m p n.toNat xs) (sorted : Increasing xs n.toNat) :
    finishes v_lower_bound.step (4 * (n.toNat + 2)) (v_lower_bound.initial p n v m)
      (fun (r, m') ↦ Partition xs n.toNat v r.toNat r.toNat ∧ m' = m) := by
  apply finishes_paths v_lower_bound.step
    (fun f ↦ match f.1 with | .b4 => true | _ => false) 4 (n.toNat + 2)
  exact finishes_of_rank segment (invariant p n v m xs) rank _
    (segments p n v m xs mem sorted) _ ⟨rfl, rfl, rfl, rfl, trivial⟩

/-- Safety and the original ACSL partition/frame postcondition, for every array length. -/
theorem correct (p : BitVec 64) (n v : BitVec 32) (m : Memory) (xs : Values)
    (mem : WordsAt m p n.toNat xs) (sorted : Increasing xs n.toNat) :
    (v_lower_bound.run p n v m).wp
      (fun (r, m') ↦ Partition xs n.toNat v r.toNat r.toNat ∧ m' = m) :=
  finishes_run _ _ _ _ (completed p n v m xs mem sorted)

/-- The same invariant also proves bounded completion of the generated program.
The bound is conservative; it is not a claim about native C instruction counts. -/
theorem terminates (p : BitVec 64) (n v : BitVec 32) (m : Memory) (xs : Values)
    (mem : WordsAt m p n.toNat xs) (sorted : Increasing xs n.toNat) :
    finishes v_lower_bound.step (8 * (n.toNat + 1) + 6)
      (v_lower_bound.initial p n v m)
      (fun (r, m') ↦ Partition xs n.toNat v r.toNat r.toNat ∧ m' = m) :=
  finishes_mono _ (by omega) _ _ (completed p n v m xs mem sorted)

end ArrayExamples.LowerBound
