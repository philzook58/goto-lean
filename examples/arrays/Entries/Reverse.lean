import Generated.Rotate

/-! The reverse entry of the shared rotation program; no second translation of its body. -/
namespace v_reverse
open GotoLean
abbrev offsetBits := v_rotate.offsetBits
abbrev Activation := v_rotate.Activation
abbrev Value := v_rotate.Value
abbrev Frame := v_rotate.Frame
abbrev Output := Unit × Memory
abbrev body := v_rotate.body
namespace Functions
namespace v_reverse
abbrev Locals := v_rotate.Functions.v_reverse.Locals
abbrev PC := v_rotate.Functions.v_reverse.PC
abbrev Frame := v_rotate.Functions.v_reverse.Frame
abbrev initial : BitVec 64 → BitVec 32 → Memory → Frame :=
  fun p n m ↦ v_rotate.Functions.v_reverse.initial p n m
end v_reverse
end Functions

def finish (value : Value) : Action Output :=
  match value with
  | .v_reverse result => pure result
  | _ => .check "internal reverse entry return type" false (.done ((), {}))
def step : Step Frame Output := callStep body finish
def initial (p : BitVec 64) (n : BitVec 32) (m : Memory := {}) : Frame :=
  (.v_reverse (Functions.v_reverse.initial p n m), [])
def run (p : BitVec 64) (n : BitVec 32) (m : Memory := {}) : Program Output :=
  GotoLean.run step (initial p n m)
def eval (p : BitVec 64) (n : BitVec 32) (fuel : Nat) (choices : List Nat := [])
    (m : Memory := {}) : Outcome Output × List Nat :=
  evalLoop step (fun frame ↦ reprStr frame.1) fuel (initial p n m) choices
end v_reverse
