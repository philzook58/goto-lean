import Proofs
import GotoLean.Audit

/-! Named feasible inputs, including ordinary parser rejection (return 0).
Ready and NUL termination are proved separately from the completed-execution certificate. -/
namespace TokenParser.Cases
open GotoLean

structure Case where
  name : String
  text : String
  capacity : Nat
  deriving Repr

def cases : List Case := [
  ⟨"empty-no-room", "", 0⟩, ⟨"empty", "", 1⟩, ⟨"space", " ", 1⟩,
  ⟨"spaces", "    ", 4⟩, ⟨"one-byte", "a", 2⟩, ⟨"one-exact", "a", 1⟩,
  ⟨"one-no-room", "a", 0⟩, ⟨"word", "cat", 4⟩, ⟨"word-exact", "cat", 3⟩,
  ⟨"trailing", "cat ", 8⟩, ⟨"leading", "  cat", 8⟩, ⟨"both", "  cat  ", 8⟩,
  ⟨"two-words", "cat dog", 8⟩, ⟨"multiple-spaces", "a   b", 8⟩,
  ⟨"tab-is-word", "\tword", 8⟩, ⟨"newline-is-word", "a\nb", 8⟩,
  ⟨"minus", "-1", 3⟩, ⟨"digits", "1234", 5⟩,
  ⟨"long-word", "abcdefghijklmnop", 17⟩, ⟨"utf8-bytes", "é", 8⟩]

private def bytes (c : Case) : Array (BitVec 8) :=
  c.text.toUTF8.data.map (fun b ↦ .ofNat 8 b.toNat) ++ #[0]
def input (c : Case) : Input := {
  memory := { objects := #[none, none, some (bytes c), some (Array.replicate c.capacity 165),
    some (Memory.unpack (Pointer.make 56 2 0 : BitVec 64))] }
  cursor := Pointer.make 56 4 0
  out := Pointer.make 56 3 0
  source := Pointer.make 56 2 0
  capacity := .ofNat 64 c.capacity
  bytes := (bytes c).toList }

private instance (m : Memory) (p : BitVec 64) (v : BitVec 64) :
    Decidable (m.ValueAt 56 p v) :=
  inferInstanceAs (Decidable (m.valid 56 p 8 = true ∧
    Memory.readBits ((m.bytes (Pointer.object 56 p)).getD #[]) (Pointer.offset 56 p) 64 = v))

/-- Every case meets the parser contract's memory premises, even if it returns failure. -/
theorem ready : ∀ c ∈ cases, Ready (input c) := by
  have checked : cases.all (fun c ↦ decide (
      (input c).memory.valid 56 (input c).source (input c).bytes.length = true ∧
      (input c).memory.ValueAt 56 (input c).cursor (input c).source ∧
      (input c).memory.valid 56 (input c).out (input c).capacity.toNat = true ∧
      Pointer.offset 56 (input c).source + (input c).bytes.length < 2^56 ∧
      Pointer.offset 56 (input c).out + (input c).capacity.toNat < 2^56)) = true := by
    decide +kernel
  simp only [List.all_eq_true, decide_eq_true_eq] at checked
  intro c hc
  obtain ⟨valid, cursor, output, inputBound, outputBound⟩ := checked c hc
  refine ⟨⟨valid, ?_⟩, cursor, output, ?_, inputBound, outputBound⟩
  · intro i hi
    have object : Pointer.object 56 (input c).source = 2 := by
      change Pointer.object 56 (Pointer.make 56 2 0 : BitVec 64) = 2
      decide +kernel
    have offset : Pointer.offset 56 (input c).source = 0 := by
      change Pointer.offset 56 (Pointer.make 56 2 0 : BitVec 64) = 0
      decide +kernel
    rw [Memory.readByte, object, offset, Nat.zero_add]
    change i < (bytes c).toList.length at hi
    change (bytes c)[i]? = some ((bytes c).toList[i]'hi)
    rw [Array.getElem_toList]
    exact Array.getElem?_eq_getElem hi
  · simp only [input]
    decide +kernel

/-- Every supplied byte string is NUL terminated, as required by the scan contract. -/
theorem terminated (c : Case) : 0 ∈ (input c).bytes := by
  simp [input, bytes]

/-- All twenty rows complete; ordinary parser rejection returns 0 instead of discarding a path. -/
theorem admitted : ∀ c ∈ cases, ∃ result,
    Executes v_take_word.step
      (v_take_word.initial (input c).cursor (input c).out (input c).capacity (input c).memory)
      (.returned result) := by
  apply replay_cases _ (fun f ↦ reprStr f.1) _ _ 200 (List.replicate 100 0)
  simp only [cases, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  repeat' apply And.intro
  all_goals decide +kernel

#guard cases.length == 20
#check_axioms ready
#check_axioms terminated
#check_axioms admitted
end TokenParser.Cases

-- A compact byte protocol lets compare.py replay these exact rows in native C.
open GotoLean

def main : IO Unit := do
  let encode (xs : Array (BitVec 8)) := ",".intercalate (xs.toList.map (toString ∘ BitVec.toNat))
  for c in TokenParser.Cases.cases do
    let i := TokenParser.Cases.input c
    let .returned (result, after) :=
      (v_take_word.eval i.cursor i.out i.capacity 200 (List.replicate 100 0) i.memory).1
      | throw (IO.userError s!"{c.name}: did not return")
    unless after.bytes 2 == i.memory.bytes 2 do throw (IO.userError "input was changed")
    let cursor := Memory.readBits ((after.bytes 4).getD #[]) 0 64
    unless Pointer.object 56 cursor == 2 do throw (IO.userError "cursor changed object")
    let source := encode ((i.memory.bytes 2).getD #[])
    let output := encode ((after.bytes 3).getD #[])
    IO.println s!"{c.name}|{source}|{c.capacity}|{result.toNat}|{Pointer.offset 56 cursor}|{output}"
