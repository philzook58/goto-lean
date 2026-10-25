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

/-- Little-endian extraction preserves available bits and chooses missing bits independently. -/
def byteExtract (site : Site) (width : Nat) (value : BitVec n) (index : Int)
    (constant : Bool) : Action (BitVec width) := do
  let offset := index * 8
  if 0 ≤ offset ∧ offset + width ≤ n then
    pure (BitVec.extractLsb' offset.toNat width value)
  else
    let unknown ← choose site width
    if !constant && index < 0 then pure unknown
    else pure ((List.range width).foldl (fun result (i : Nat) ↦
      let bit := offset + (i : Int)
      if 0 ≤ bit ∧ bit < n then
        replaceBits result i (BitVec.extractLsb' bit.toNat 1 value)
      else result) unknown)

/-- CBMC's constant updates require the truncated field to fit; variable updates clip at the end. -/
def byteUpdate (old : BitVec n) (index : Int) (value : BitVec w)
    (constant : Bool) : BitVec n :=
  if 0 ≤ index ∧ (!constant || index * 8 + min n w ≤ n) then
    replaceBits old (index.toNat * 8) value
  else old

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
