import GotoLean.Basic

namespace GotoLean
open Std.WP Lean.Order

/-- Replace a packed field; bits outside the field retain their old values. -/
def replaceBits (old : BitVec n) (offset : Nat) (value : BitVec w) : BitVec n :=
  let mask := shiftLeft (BitVec.setWidth n (~~~(0 : BitVec w))) offset
  (old &&& ~~~mask) ||| shiftLeft (BitVec.setWidth n value) offset

/-- A finite array whose elements all contain the same bit pattern. -/
def arrayOf (count : Nat) (value : BitVec w) : BitVec (count * w) :=
  (List.range count).foldl
    (fun result i => result ||| shiftLeft (BitVec.setWidth (count * w) value) (i * w)) 0

/-- CBMC's finite-array encoding leaves reads outside the array unconstrained.
Bounds assertions must be supplied in the GOTO input when proving array safety. -/
def arrayRead (site : Site) (count width : Nat) (value : BitVec n) (index : Int) :
    Action (BitVec width) :=
  if 0 ≤ index ∧ index < count then
    pure (BitVec.extractLsb' (index.toNat * width) width value)
  else choose site width

@[spec] theorem arrayRead_spec (site : Site) (count width : Nat) (value : BitVec n)
    (index : Int) (Q : BitVec width → Prop) :
    ⦃if 0 ≤ index ∧ index < count then
      Q (BitVec.extractLsb' (index.toNat * width) width value) else ∀ v, Q v⦄
    arrayRead site count width value index ⦃Q⦄ := by
  constructor
  intro h
  by_cases hi : 0 ≤ index ∧ index < count <;>
    simpa [arrayRead, hi, choose, Action.wp] using h

end GotoLean
