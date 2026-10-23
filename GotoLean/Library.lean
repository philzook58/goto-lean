import GotoLean.Memory

namespace GotoLean.Memory

/-- memcpy requires disjoint byte ranges, even when they share an object. -/
def disjoint (offsetBits : Nat) (dst src : BitVec w) (size : Nat) : Bool :=
  Pointer.object offsetBits dst != Pointer.object offsetBits src ||
    decide (Pointer.offset offsetBits dst + size ≤ Pointer.offset offsetBits src ∨
      Pointer.offset offsetBits src + size ≤ Pointer.offset offsetBits dst)

def copyBytes (dst : Array (BitVec 8)) (offset : Nat) (src : Array (BitVec 8)) :
    Array (BitVec 8) :=
  (List.range src.size).foldl (fun b i => b.setIfInBounds (offset + i) src[i]!) dst

def copied (m : Memory) (offsetBits : Nat) (dst src : BitVec w) (size : Nat) : Memory :=
  let source := ((m.bytes (Pointer.object offsetBits src)).getD #[]).extract
    (Pointer.offset offsetBits src) (Pointer.offset offsetBits src + size)
  m.put (Pointer.object offsetBits dst)
    (copyBytes ((m.bytes (Pointer.object offsetBits dst)).getD #[])
      (Pointer.offset offsetBits dst) source)

/-- A checked, snapshot-based memcpy: preserve other bytes and return the destination pointer.
Null/dead pointers are rejected even for a zero-length copy. -/
def memcpy (site : Site) (offsetBits : Nat) (m : Memory) (dst src : BitVec w) (size : Nat) :
    Action (BitVec w × Memory) := do
  check (site ++ "; memcpy source") (m.valid offsetBits src size)
  check (site ++ "; memcpy destination") (m.valid offsetBits dst size)
  check (site ++ "; memcpy overlap") (disjoint offsetBits dst src size)
  pure (dst, copied m offsetBits dst src size)

/-- Bytes from a pointer to the end of its object; a terminator must occur in that range. -/
def stringBytes (m : Memory) (offsetBits : Nat) (p : BitVec w) : Array (BitVec 8) :=
  let b := (m.bytes (Pointer.object offsetBits p)).getD #[]
  b.extract (Pointer.offset offsetBits p) b.size

def stringLength (m : Memory) (offsetBits : Nat) (p : BitVec w) : Nat :=
  (stringBytes m offsetBits p).toList.findIdx (· == 0)

/-- strlen reads through the first NUL; unterminated or invalid objects fail explicitly. -/
def strlen (site : Site) (offsetBits width : Nat) (m : Memory) (p : BitVec w) :
    Action (BitVec width) := do
  check (site ++ "; strlen pointer") (m.valid offsetBits p 1)
  let n := stringLength m offsetBits p
  check (site ++ "; strlen terminator") (decide (n < (stringBytes m offsetBits p).size))
  pure (BitVec.ofNat width n)

open Std.WP Lean.Order

@[spec] theorem memcpy_spec (site : Site) (offsetBits : Nat) (m : Memory)
    (dst src : BitVec w) (size : Nat) (Q : BitVec w × Memory → Prop) :
    ⦃m.valid offsetBits src size = true ∧ m.valid offsetBits dst size = true ∧
      disjoint offsetBits dst src size = true ∧ Q (dst, copied m offsetBits dst src size)⦄
    memcpy site offsetBits m dst src size ⦃Q⦄ := ⟨id⟩

@[spec] theorem strlen_spec (site : Site) (offsetBits width : Nat) (m : Memory)
    (p : BitVec w) (Q : BitVec width → Prop) :
    ⦃m.valid offsetBits p 1 = true ∧
      decide (stringLength m offsetBits p < (stringBytes m offsetBits p).size) = true ∧
      Q (BitVec.ofNat width (stringLength m offsetBits p))⦄
    strlen site offsetBits width m p ⦃Q⦄ := ⟨id⟩

end GotoLean.Memory
