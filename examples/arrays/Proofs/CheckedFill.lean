import GotoLean.Audit
import Spec.CheckedFill
import GotoLean.Paths
import Proofs.Array

namespace ArrayExamples.CheckedFill
open GotoLean

private theorem object_bits_ne (p q : BitVec 64) (h : Pointer.object 56 p ≠ Pointer.object 56 q) :
    BitVec.ofNat 64 (Pointer.object 56 p) ≠ BitVec.ofNat 64 (Pointer.object 56 q) := by
  have bound (r : BitVec 64) : Pointer.object 56 r < 2^64 := by
    have hr := r.isLt
    simp only [Pointer.object, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    omega
  intro eq
  apply h
  have same := congrArg BitVec.toNat eq
  simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (bound p),
    Nat.mod_eq_of_lt (bound q)] using same

private theorem offset_expression (p : BitVec 64) (i n : BitVec 32)
    (lt : i.toNat < n.toNat) (nowrap : Pointer.offset 56 p + 4*n.toNat < 2^56) :
    ((p.setWidth 56).setWidth 64 + i.setWidth 64 * 4).toNat =
      Pointer.offset 56 p + 4*i.toNat := by
  have hi := i.isLt
  have hp := (p.setWidth 56).isLt
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_setWidth]
  change ((p.toNat % 2^56) % 2^64 + (i.toNat % 2^64 * 4) % 2^64) % 2^64 = _
  simp only [Pointer.offset, BitVec.toNat_setWidth] at nowrap ⊢
  omega

private theorem objectState_written (m : Memory) (p q : BitVec 64) (value : BitVec 32)
    (state : ArrayExamples.CheckedSpec.ObjectState m p)
    (valid : m.valid 56 q 4 = true) :
    ArrayExamples.CheckedSpec.ObjectState (m.written 56 q value) p := by
  refine ⟨?_, ?_, ?_⟩
  · intro bytes hb
    have sizes := Memory.written_extent m 56 q value valid (Pointer.object 56 p)
    rw [hb] at sizes
    cases old : m.bytes (Pointer.object 56 p) with
    | none => simp [old] at sizes
    | some b =>
      have same : bytes.size = b.size := by simpa [old] using sizes
      rw [same]
      exact state.sizeFits b old
  · simpa [Memory.written, Memory.put, Memory.getGlobal] using state.notDeallocated
  · simpa [Memory.written, Memory.put, Memory.getGlobal] using state.notDead

private theorem store_step (s : v_fill.Locals)
    (lt : s.v_i.toNat < s.v_n.toNat)
    (nowrap : Pointer.offset 56 s.v_a + 4*s.v_n.toNat < 2^56)
    (state : CheckedSpec.ObjectState s.memory s.v_a)
    (valid : s.memory.valid 56 (address s.v_a s.v_i.toNat) 4 = true)
    (Q : Next v_fill.Frame v_fill.Output → Prop) :
    (v_fill.step (.b3, s)).wp Q ↔
      Q (.inl (.b2, { s with
        v_i := s.v_i + 1
        memory := s.memory.written 56 (address s.v_a s.v_i.toNat) s.v_v })) := by
  obtain ⟨b, hb, ho, extent⟩ := (Memory.valid_iff ..).mp valid
  simp only [address, Pointer.object_add] at hb ho
  unfold address at extent
  rw [Pointer.offset_add_nat s.v_a (4*s.v_i.toNat) (by decide) (by omega)] at extent
  have nonnull := object_bits_ne (0 : BitVec 64) s.v_a
    (by change 0 ≠ Pointer.object 56 s.v_a; omega)
  have notInvalid : Pointer.object 56 s.v_a ≠ 1 := by omega
  have freed := object_bits_ne s.v_a
    (s.memory.getGlobal "__CPROVER_deallocated" (0 : BitVec 64)) state.notDeallocated
  have dead := object_bits_ne s.v_a
    (s.memory.getGlobal "__CPROVER_dead_object" (0 : BitVec 64)) state.notDead
  have offset := offset_expression s.v_a s.v_i s.v_n lt nowrap
  have sizeFits := state.sizeFits b hb
  have bounds : BitVec.ule
      (((s.v_a.setWidth 56).setWidth 64 + s.v_i.setWidth 64 * 4).setWidth 65 + 4)
      ((BitVec.ofNat 64 b.size).setWidth 65) = true := by
    simp only [BitVec.ule, decide_eq_true_eq, BitVec.toNat_add,
      BitVec.toNat_setWidth, BitVec.toNat_ofNat, offset]
    change ((Pointer.offset 56 s.v_a + 4*s.v_i.toNat) % 2^65 + 4) % 2^65 ≤
      b.size % 2^64 % 2^65
    omega
  simp only [v_fill.step, Bind.bind, Action.wp_bind, check, Action.wp, Action.wp_pure,
    v_fill.offsetBits, Memory.objectSize, hb, index_address, Memory.store_wp]
  constructor
  · rintro ⟨_, _, _, _, _, _, _, result⟩
    exact result
  · intro result
    exact ⟨by simpa using nonnull, by simpa using notInvalid,
      by simpa using freed, by simpa using dead, bounds,
      by simp only [Bool.or_eq_true]; exact Or.inl (by simpa using nonnull), valid, result⟩

private def view (xs : Values) (v : BitVec 32) (i : Nat) : Values :=
  fun j ↦ if j < i then v else xs j

private def cut (f : v_fill.Frame) := match f.1 with | .b2 => true | _ => false
private def invariant (p : BitVec 64) (n v : BitVec 32) (before : Memory) (xs : Values)
    (f : v_fill.Frame) : Prop :=
  let s := f.2
  s.v_a = p ∧ s.v_n = n ∧ s.v_v = v ∧
  (0 < n.toNat → CheckedSpec.ObjectState s.memory p) ∧
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
  obtain ⟨ha, hn, hv, state, hi⟩ := hi
  dsimp only at ha hn hv
  cases pc <;> dsimp only at hi
  all_goals try exact hi.elim
  case b0 =>
    obtain ⟨hm, mem⟩ := hi
    simp only [path, v_fill.step, cut, Bind.bind, Action.wp_bind, choose, Action.wp,
      Action.wp_pure, ↓reduceIte, Sum.elim, invariant, rank]
    intro choice
    refine ⟨⟨ha, hn, hv, state, by simp, ?_, ?_⟩, ?_⟩
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
      simp only [cut, Bool.false_eq_true, ↓reduceIte, path,
        Bind.bind, Action.wp_bind, Action.wp_pure]
      rw [store_step s (by simpa [hn] using lt) (by simpa [ha, hn] using nowrap)
        (by simpa [ha] using state (by omega)) (by simpa [ha] using valid)]
      simp only [↓reduceIte, Action.wp_pure, Sum.elim, invariant, rank]
      rw [ha, hv]
      refine ⟨⟨by trivial, hn, by trivial, ?_, by rw [inc]; omega, ?_, ?_⟩, ?_⟩
      · intro positive
        exact objectState_written s.memory p _ v (state positive) valid
      · have updated := wordsAt_written s.memory p n.toNat _ mem nowrap _ lt v
        intro j hj
        have eq : (if j = s.v_i.toNat then v else view xs v s.v_i.toNat j) =
            view xs v (s.v_i.toNat+1) j := by unfold view; grind
        simpa only [inc, eq] using updated j hj
      · exact frame_written before s.memory p n.toNat frame _ lt nowrap v valid
      · simp only [hn, inc]; omega

/-- Safety, contents, byte framing and bounded completion for every representable length. -/
theorem verify (p : BitVec 64) (n v : BitVec 32) (m : Memory) (xs : Values)
    (mem : WordsAt m p n.toNat xs) (nowrap : Pointer.offset 56 p + 4*n.toNat < 2^56)
    (state : 0 < n.toNat → CheckedSpec.ObjectState m p) :
    finishes v_fill.step (2*(n.toNat+2)) (v_fill.initial p n v m)
      (fun (_, after) ↦ Filled m after p n.toNat v) := by
  apply finishes_paths v_fill.step cut 2 (n.toNat+2)
  exact finishes_of_rank _ (invariant p n v m xs) rank _ (segments p n v m xs nowrap)
    _ ⟨rfl, rfl, rfl, state, rfl, mem⟩

/-- The reviewable contract holds for the actual instrumented entry point. -/
theorem implements : CheckedSpec.fill := by
  intro p n v m xs mem nowrap state
  exact ⟨2*(n.toNat+2), verify p n v m xs mem nowrap state⟩

/-- Unbounded safety and functional correctness of the instrumented program. -/
theorem safe (p : BitVec 64) (n v : BitVec 32) (m : Memory) (xs : Values)
    (mem : WordsAt m p n.toNat xs) (nowrap : Pointer.offset 56 p + 4*n.toNat < 2^56)
    (state : 0 < n.toNat → CheckedSpec.ObjectState m p) :
    (v_fill.run p n v m).wp (fun (_, after) ↦ Filled m after p n.toNat v) :=
  finishes_run _ _ _ _ (verify p n v m xs mem nowrap state)

/-- Zero-length fill needs neither a nonnull pointer nor a live allocation. -/
theorem empty (v : BitVec 32) (m : Memory) :
    finishes v_fill.step 4 (v_fill.initial 0 0 v m) (fun (_, after) ↦ after = m) := by
  simp [finishes, v_fill.step, v_fill.initial, Bind.bind, Action.wp_bind, choose, Action.wp]

#check_axioms verify
#check_axioms implements
#check_axioms safe
#check_axioms empty

end ArrayExamples.CheckedFill
