import Spec.Caller
import Proofs.CheckedFill
import GotoLean.CallSummary

namespace ArrayExamples.Caller
open GotoLean

-- Transfer the already-proved fill contract to the copy in the caller's call stack.
private def embed (f : v_fill.Frame) : v_fill_local.Frame :=
  let (pc, s) := f
  let pc' : v_fill_local.Functions.v_fill.PC := match pc with
    | .b0 => .b0 | .b2 => .b2 | .b3 => .b3 | .b12 => .b12
  (.v_fill (pc', {
    v_a := s.v_a
    v_n := s.v_n
    v_v := s.v_v
    v_i := s.v_i
    memory := s.memory
    result := s.result }), [])

private def fillFinish : v_fill_local.Value → Action v_fill.Output
  | .v_fill value => pure value
  | _ => do check "wrong callee return" false; pure ((), {})

private theorem fill_step (f : v_fill.Frame)
    (Q : Next v_fill_local.Frame v_fill.Output → Prop) :
    (callStep v_fill_local.body fillFinish (embed f)).wp Q =
    (v_fill.step f).wp (fun next ↦ Q (next.map embed id)) := by
  rcases f with ⟨pc, s⟩
  cases pc <;>
    simp [embed, callStep, v_fill_local.body, v_fill.step, fillFinish, Bind.bind, Sum.map,
      Memory.store, Memory.objectSize,
      Action.wp_bind, Action.wp_pure, choose, check, Action.wp]
  split <;> rfl

private theorem fill_finishes (fuel : Nat) (f : v_fill.Frame) (Q : v_fill.Output → Prop)
    (h : finishes v_fill.step fuel f Q) :
    finishes (callStep v_fill_local.body fillFinish) fuel (embed f) Q := by
  induction fuel generalizing f with
  | zero => exact False.elim h
  | succ fuel ih =>
    change (callStep v_fill_local.body fillFinish (embed f)).wp _
    change (v_fill.step f).wp _ at h
    rw [fill_step]
    apply Action.wp_mono _ _ h
    intro next hn
    cases next with
    | inl f' => exact ih f' hn
    | inr value => exact hn

private def pointer : BitVec 64 := Pointer.make 56 2 0
private def allocated (bits : BitVec 128) : Memory :=
  { objects := #[none, none, some (Memory.unpack bits)] }

private theorem allocation_words (bits : BitVec 128) :
    WordsAt (allocated bits) pointer 4 (fun i ↦ Memory.readBits (Memory.unpack bits) (4*i) 32) := by
  intro i hi
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases cases with rfl | rfl | rfl | rfl <;>
    simp [Memory.ValueAt, Memory.valid, Memory.bytes, allocated, pointer, address,
      Pointer.add, Pointer.make, Pointer.object, Pointer.offset, Memory.unpack, shiftLeft_eq]

private theorem allocation_state (bits : BitVec 128) :
    CheckedSpec.ObjectState (allocated bits) pointer := by
  constructor <;>
    simp [allocated, pointer, Pointer.object, Pointer.make, Memory.bytes,
      Memory.getGlobal, Memory.unpack, shiftLeft_eq]

private theorem call_fill (value : BitVec 32) (bits : BitVec 128)
    (resume : v_fill_local.Value → Action v_fill_local.Activation) (tail : Nat)
    (Q : v_fill_local.Output → Prop)
    (returns : ∀ after, WordsAt after pointer 4 (fun _ ↦ value) →
      (resume (.v_fill ((), after))).wp
        (fun frame ↦ finishes v_fill_local.step tail (frame, []) Q)) :
    finishes v_fill_local.step (12+tail)
      (.v_fill (v_fill_local.Functions.v_fill.initial pointer 4 value (allocated bits)), [resume])
      Q := by
  have verified := CheckedFill.verify pointer 4 value (allocated bits) _ (allocation_words bits)
    (by decide +kernel) (fun _ ↦ allocation_state bits)
  have lifted := fill_finishes 12 _ _ verified
  apply finishes_resume v_fill_local.body fillFinish v_fill_local.finish resume [] tail
    (fun (_, after) ↦ CheckedFill.Filled (allocated bits) after pointer 4 value) Q ?_ 12 _ [] lifted
  intro result valid
  cases result with
  | v_fill output =>
    rcases output with ⟨u, after⟩
    cases u
    exact returns after valid.1
  | v_fill_local output => simp [fillFinish, check, Action.wp, Bind.bind] at valid

private theorem returned (value : BitVec 32) (after : Memory)
    (words : WordsAt after pointer 4 (fun _ ↦ value)) :
    finishes v_fill_local.step 1
      (.v_fill_local (.b2, { v_value := value, v_a := pointer, memory := after }), [])
      (fun (result, final) ↦ result = value ∧ final.bytes 2 = none) := by
  have first := words 0 (by decide)
  have last := words 3 (by decide)
  simp only [address, show (4*0 : Nat) = 0 from rfl,
    show (4*3 : Nat) = 12 from rfl] at first last
  simp only [finishes, v_fill_local.step, callStep, v_fill_local.body, Bind.bind,
    Action.wp_bind, Action.wp_pure, v_fill_local.offsetBits]
  simp only [show (BitVec.signExtend 64 (0 : BitVec 32)).toInt * 4 = 0 from by decide +kernel,
    show (BitVec.signExtend 64 (3 : BitVec 32)).toInt * 4 = 12 from by decide +kernel]
  change after.ValueAt 56 (Pointer.add 56 pointer 0) value at first
  change after.ValueAt 56 (Pointer.add 56 pointer 12) value at last
  have readFirst (site : Site) (Q : BitVec 32 → Prop) :=
    Memory.load_value site after 56 _ value first Q
  have readLast (site : Site) (Q : BitVec 32 → Prop) :=
    Memory.load_value site after 56 _ value last Q
  simp only [readFirst, readLast]
  simp [v_fill_local.finish, choose, check, Action.wp, Memory.release,
    Memory.bytes, Memory.setGlobal, pointer, Pointer.object, Pointer.make, shiftLeft_eq]

private def resume (value : BitVec 32) (bits : BitVec 128) :
    v_fill_local.Value → Action v_fill_local.Activation
  | .v_fill (_, after) =>
    pure (.v_fill_local (.b2, { v_a := pointer, v_value := value, memory := after }))
  | _ => do
    check "fill_local: GOTO 43; caller.c:6; internal return type" false
    pure (.v_fill_local (.b2, { v_a := pointer, v_value := value, memory := allocated bits }))

-- Check the allocation block with an abstract continuation, without unfolding the loop.
private theorem entry_wp (value : BitVec 32) (Q : Next v_fill_local.Frame v_fill_local.Output → Prop) :
    (v_fill_local.step (v_fill_local.initial value)).wp Q ↔
    ∀ bits, Q (.inl (.v_fill
      (v_fill_local.Functions.v_fill.initial pointer 4 value (allocated bits)),
      [resume value bits])) := by
  unfold resume
  simp [v_fill_local.step, callStep, v_fill_local.initial,
    v_fill_local.Functions.v_fill_local.initial, v_fill_local.body, Bind.bind,
    Action.wp_bind, Action.wp_pure, Memory.alloc, choose, check, Action.wp,
    v_fill_local.offsetBits, v_fill_local.objectBits, pointer, allocated,
    Pointer.add, Pointer.make, Pointer.object, shiftLeft_eq]
  rfl

/-- The actual C caller establishes fill's memory premises and completes for every input value. -/
theorem implements : CallerSpec.fill_local := by
  intro value
  refine ⟨14, ?_⟩
  rw [finishes, entry_wp]
  intro bits
  simp only [Sum.elim_inl]
  apply call_fill value bits (resume value bits) 1
  intro after words
  exact returned value after words

/-- A reachable failure of the buggy caller's imported assertion on input 1. -/
theorem underfill : CallerSpec.underfill := by
  let out := (v_fill_local_bug.eval 1 20 [0, 0]).1
  have failed : (match out with
    | .assertionFailed site =>
      site.toSlice.endsWith "; property fill_local_bug.assertion.1; underfilled array"
    | _ => false) = true := by decide +kernel
  have execution := evalLoop_exec v_fill_local_bug.step (fun frame ↦ reprStr frame.1)
    20 (v_fill_local_bug.initial 1) [0, 0]
  change out.Corresponds (Executes v_fill_local_bug.step (v_fill_local_bug.initial 1)) at execution
  cases h : out <;> simp [h] at failed
  exact ⟨_, failed, by simpa [h, Outcome.Corresponds] using execution⟩

-- A feasible successful run accompanies the universal theorem and the negative control.
#guard (v_fill_local.eval 9 20 [0, 0, 0]).1 matches .returned (9, _)
#check_axioms implements
#check_axioms underfill

end ArrayExamples.Caller
