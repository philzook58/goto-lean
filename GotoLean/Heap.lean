import GotoLean.Memory

namespace GotoLean.Memory

/-- CBMC's allocation primitive always succeeds, with zero or arbitrary initial bytes.
Finite pointer capacity remains an explicit model check. -/
def allocate (site : Site) (offsetBits objectBits : Nat) (m : Memory)
    (size : Nat) (zero : Bool) : Action (BitVec (offsetBits + objectBits) × Memory) := do
  check (site ++ "; allocation capacity")
    (decide (2 ≤ m.objects.size ∧ m.objects.size < 2^objectBits ∧ size < 2^offsetBits))
  let bits ← if zero then pure (0 : BitVec (8*size))
    else choose (site ++ "; initial heap bytes") (8*size)
  pure (Pointer.make offsetBits m.objects.size 0,
    { m with objects := m.objects.push (some (unpack bits)), heap := m.objects.size :: m.heap })

/-- The r/w/rw_ok range predicate, including CBMC's tracked dead/deallocated objects.
The current object store additionally rejects unavailable objects. -/
def rwOk (offsetBits : Nat) (m : Memory) (p : BitVec w) (size : Nat)
    (deallocated dead : BitVec w) : Bool :=
  m.valid offsetBits p size && decide (0 ≤ (p.setWidth offsetBits).toInt) &&
    (Pointer.object offsetBits p != Pointer.object offsetBits deallocated) &&
    (Pointer.object offsetBits p != Pointer.object offsetBits dead)

/-- External malloc model: failure or fresh storage with arbitrary bytes.
Zero-sized allocations may succeed. IDs are finite and never reused. -/
def malloc (site : Site) (offsetBits objectBits : Nat) (m : Memory) (size : Nat) :
    Action (BitVec (offsetBits + objectBits) × Memory) := do
  let succeeds ← choose (site ++ "; allocation succeeds") 1
  if succeeds == 0 then return (0, m)
  allocate site offsetBits objectBits m size false

/-- Only a live heap object's base may be freed; null is a no-op. -/
def free (site : Site) (offsetBits : Nat) (m : Memory) (p : BitVec w) : Action Memory := do
  if p == 0 then return m
  check (site ++ "; free live heap base")
    (decide (1 < Pointer.object offsetBits p ∧ Pointer.offset offsetBits p = 0) &&
      m.heap.contains (Pointer.object offsetBits p) &&
      (m.bytes (Pointer.object offsetBits p)).isSome)
  pure ((m.release offsetBits p).setGlobal "__CPROVER_deallocated" p)

end GotoLean.Memory
