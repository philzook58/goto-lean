import GotoLean.Audit
import Proofs

open GotoLean TokenParser

private def text : Array (BitVec 8) := #[32, 32, 104, 105, 32, 116, 104, 101, 114, 101, 0]

def exampleInput : Input := {
  memory := { objects := #[none, none, some text, some (Array.replicate 16 165),
    some (Memory.unpack (Pointer.make 56 2 0 : BitVec 64))] }
  cursor := Pointer.make 56 4 0
  out := Pointer.make 56 3 0
  source := Pointer.make 56 2 0
  capacity := 16
  bytes := text.toList }

theorem exampleReady : Ready exampleInput := by
  constructor
  · constructor
    · decide +kernel
    · intro i hi
      have object : Pointer.object 56 exampleInput.source = 2 := by decide +kernel
      have offset : Pointer.offset 56 exampleInput.source = 0 := by decide +kernel
      have contents : exampleInput.memory.bytes 2 = some text := by rfl
      dsimp only [exampleInput] at hi object offset contents ⊢
      rw [Memory.readByte, object, offset, Nat.zero_add, contents]
      change text[i]? = some text.toList[i]
      rw [Array.getElem_toList]
      exact Array.getElem?_eq_getElem hi
  · constructor <;> decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel

def exampleScan := scan exampleInput.bytes (by decide)

/-- This client uses the proved parser contract, without PCs, fuel or interpreter unfolding. -/
theorem exampleCorrect :
    (v_take_word.run exampleInput.cursor exampleInput.out exampleInput.capacity
      exampleInput.memory).wp
      (Parsed exampleInput exampleScan) :=
  success exampleInput exampleScan exampleReady (by decide +kernel)

def main : IO Unit := do
  let input := exampleInput
  let (result, _) :=
    v_take_word.eval input.cursor input.out input.capacity 100 [0, 0, 0] input.memory
  unless result == .returned (expected input exampleScan) do
    throw (IO.userError "execution disagrees with the proved specification")
  match result with
  | .returned (ok, memory) =>
    let bytes := (memory.bytes 3).getD #[] |>.toList.map BitVec.toNat
    IO.println s!"returned {ok.toNat}; output bytes: {bytes}"
    IO.println s!"word [{exampleScan.start}, {exampleScan.stop}); next input: {exampleScan.next}"
  | _ => throw (IO.userError (reprStr result))

#check_axioms exampleCorrect
