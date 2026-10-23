import GotoLean.Audit
import Generated.TakeWord
import WordMain

open GotoLean

private def input : Array (BitVec 8) := #[32, 32, 104, 105, 32, 116, 104, 101, 114, 101, 0]
private def inputPointer : BitVec 64 := Pointer.make 56 2 0
private def outputPointer : BitVec 64 := Pointer.make 56 3 0
private def cursorPointer : BitVec 64 := Pointer.make 56 4 0
private def memory : Memory := { objects := #[none, none, some input,
  some (Array.replicate 16 165), some (Memory.unpack inputPointer)] }
private def copied : Memory := { objects := #[none, none, some input,
  some (#[104, 105, 0] ++ Array.replicate 13 165),
  some (Memory.unpack (Pointer.add 56 inputPointer 5))] }

/-- The actual helper copies "hi", appends NUL, preserves other bytes and advances the cursor. -/
theorem take_word_execution : Executes v_take_word.step
    (v_take_word.initial cursorPointer outputPointer 16 memory) (.returned (1, copied)) := by
  have h := evalLoop_exec v_take_word.step (fun f => reprStr f.1) 100
    (v_take_word.initial cursorPointer outputPointer 16 memory) [0, 0, 0]
  have evaluated : (v_take_word.eval cursorPointer outputPointer 16 100 [0, 0, 0] memory).1 =
      .returned (1, copied) := by decide +kernel
  rw [show (evalLoop v_take_word.step (fun f => reprStr f.1) 100
    (v_take_word.initial cursorPointer outputPointer 16 memory) [0, 0, 0]).1 = _
    from evaluated] at h
  exact h

-- Execute the original harness too, including its successful strlen/cursor assertions.
private def harnessChoices : List Nat :=
  [0, 0, 0] ++ ((input.toList.map BitVec.toNat ++ List.replicate 99 0).take 99).flatMap
    (fun byte => [0, byte]) ++ List.replicate 20 0
#guard (v_main.eval 1000 harnessChoices).1 matches .returned (0, _)

#check_axioms take_word_execution
