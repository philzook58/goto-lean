import GotoLean.MemoryViews

/-! A small view of C `int` arrays. Values retain their signed 32-bit representation. -/
namespace ArrayExamples
open GotoLean

abbrev Values := Nat → BitVec 32

def address (p : BitVec 64) (i : Nat) : BitVec 64 := Pointer.add 56 p (Int.ofNat (4 * i))

def WordsAt (m : Memory) (p : BitVec 64) (n : Nat) (xs : Values) : Prop :=
  ∀ i, i < n → m.ValueAt 56 (address p i) (xs i)

def Increasing (xs : Values) (n : Nat) : Prop :=
  ∀ i j, i ≤ j → j < n → (xs i).toInt ≤ (xs j).toInt

/-- The ACSL lower-bound postcondition, using mathematical indices and signed values. -/
def Partition (xs : Values) (n : Nat) (v : BitVec 32) (left right : Nat) : Prop :=
  left ≤ right ∧ right ≤ n ∧
    (∀ i, i < left → (xs i).toInt < v.toInt) ∧
    (∀ i, right ≤ i → i < n → v.toInt ≤ (xs i).toInt)

/-- A byte frame includes padding, adjacent arrays, and all other objects. -/
def Frame (before after : Memory) (p : BitVec 64) (n : Nat) : Prop :=
  ∀ object offset, object ≠ Pointer.object 56 p ∨ offset < Pointer.offset 56 p ∨
    Pointer.offset 56 p + 4*n ≤ offset →
    after.readByte object offset = before.readByte object offset

end ArrayExamples
