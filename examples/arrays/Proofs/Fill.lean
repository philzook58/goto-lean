import Generated.Fill
import GotoLean.Paths
import Proofs.Array

namespace ArrayExamples.Fill
open GotoLean

private def view (xs : Values) (v : BitVec 32) (i : Nat) : Values :=
  fun j ↦ if j < i then v else xs j

private def cut (f : v_fill.Frame) := match f.1 with | .b2 => true | _ => false
private def invariant (p : BitVec 64) (n v : BitVec 32) (before : Memory) (xs : Values)
    (f : v_fill.Frame) : Prop :=
  let s := f.2
  s.v_a = p ∧ s.v_n = n ∧ s.v_v = v ∧
  match f.1 with
  | .b0 => s.memory = before ∧ WordsAt before p n.toNat xs
  | .b2 => s.v_i.toNat ≤ n.toNat ∧
      WordsAt s.memory p n.toNat (view xs v s.v_i.toNat) ∧ Frame before s.memory p n.toNat
  | _ => False
private def rank (f : v_fill.Frame) :=
  match f.1 with | .b0 => f.2.v_n.toNat+1 | _ => f.2.v_n.toNat-f.2.v_i.toNat

/-- The fill contract includes every surrounding byte, not just the array contents. -/
def Filled (before after : Memory) (p : BitVec 64) (n : Nat) (v : BitVec 32) : Prop :=
  WordsAt after p n (fun _ ↦ v) ∧ Frame before after p n

private theorem segments (p : BitVec 64) (n v : BitVec 32) (before : Memory) (xs : Values)
    (nowrap : Pointer.offset 56 p + 4*n.toNat < 2^56)
    (f : v_fill.Frame) (hi : invariant p n v before xs f) :
    (path v_fill.step cut 2 f).wp
      (Sum.elim (fun next ↦ invariant p n v before xs next ∧ rank next < rank f)
        (fun (_, after) ↦ Filled before after p n.toNat v)) := by
  rcases f with ⟨pc, s⟩
  obtain ⟨ha, hn, hv, hi⟩ := hi
  dsimp only at ha hn hv
  cases pc <;> dsimp only at hi
  all_goals try exact hi.elim
  case b0 =>
    obtain ⟨hm, mem⟩ := hi
    simp only [path, v_fill.step, cut, Bind.bind, Action.wp_bind, choose, Action.wp,
      Action.wp_pure, ↓reduceIte, Sum.elim, invariant, rank]
    intro choice
    refine ⟨⟨ha, hn, hv, by simp, ?_, ?_⟩, ?_⟩
    · intro j hj
      simpa [hm, view] using mem j hj
    · simpa [hm] using frame_refl before p n.toNat
    · simp [hn]
  case b2 =>
    obtain ⟨bound, mem, frame⟩ := hi
    unfold path
    simp only [v_fill.step, Bind.bind, Action.wp_bind]
    split
    · rename_i stop
      have eq : s.v_i.toNat = n.toNat := by simp_all [BitVec.ult]; omega
      simp only [cut, Bool.false_eq_true, ↓reduceIte, path, v_fill.step,
        Bind.bind, Action.wp_bind, Action.wp_pure, Sum.elim]
      refine ⟨?_, frame⟩
      intro j hj
      simpa [view, eq, hj] using mem j hj
    · rename_i continuing
      have lt : s.v_i.toNat < n.toNat := by simpa [BitVec.ult, hn] using continuing
      have valid := (mem s.v_i.toNat lt).1
      have inc := index_increment s.v_i n lt
      simp only [cut, Bool.false_eq_true, ↓reduceIte, path, v_fill.step,
        Bind.bind, Action.wp_bind, Action.wp_pure, Sum.elim]
      rw [ha, hv, index_address, Memory.store_wp]
      refine ⟨valid, ?_⟩
      simp only [invariant, rank]
      refine ⟨⟨by trivial, hn, by trivial, by rw [inc]; omega, ?_, ?_⟩, ?_⟩
      · have updated := wordsAt_written s.memory p n.toNat _ mem nowrap _ lt v
        intro j hj
        have eq : (if j = s.v_i.toNat then v else view xs v s.v_i.toNat j) =
            view xs v (s.v_i.toNat+1) j := by unfold view; grind
        simpa only [inc, eq] using updated j hj
      · exact frame_written before s.memory p n.toNat frame _ lt nowrap v valid
      · simp only [hn, inc]; omega

/-- Safety, contents, byte framing and bounded completion for every representable length. -/
theorem verify (p : BitVec 64) (n v : BitVec 32) (m : Memory) (xs : Values)
    (mem : WordsAt m p n.toNat xs) (nowrap : Pointer.offset 56 p + 4*n.toNat < 2^56) :
    finishes v_fill.step (2*(n.toNat+2)) (v_fill.initial p n v m)
      (fun (_, after) ↦ Filled m after p n.toNat v) := by
  apply finishes_paths v_fill.step cut 2 (n.toNat+2)
  exact finishes_of_rank _ (invariant p n v m xs) rank _ (segments p n v m xs nowrap)
    _ ⟨rfl, rfl, rfl, rfl, mem⟩

end ArrayExamples.Fill
