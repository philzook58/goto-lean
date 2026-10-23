import GotoLean.Memory

namespace GotoLean.Memory

/-- External malloc model: failure or fresh storage with arbitrary bytes.
Zero-sized allocations may succeed. IDs are finite and never reused. -/
def malloc (site : Site) (offsetBits objectBits : Nat) (m : Memory) (size : Nat) :
    Action (BitVec (offsetBits + objectBits) × Memory) := do
  let succeeds ← choose (site ++ "; allocation succeeds") 1
  if succeeds == 0 then return (0, m)
  check (site ++ "; allocation capacity")
    (decide (2 ≤ m.objects.size ∧ m.objects.size < 2^objectBits ∧ size < 2^offsetBits))
  let bits ← choose (site ++ "; initial heap bytes") (8*size)
  pure (Pointer.make offsetBits m.objects.size 0,
    { m with objects := m.objects.push (some (unpack bits)), heap := m.objects.size :: m.heap })

/-- Only a live heap object's base may be freed; null is a no-op. -/
def free (site : Site) (offsetBits : Nat) (m : Memory) (p : BitVec w) : Action Memory := do
  if p == 0 then return m
  check (site ++ "; free live heap base")
    (decide (1 < Pointer.object offsetBits p ∧ Pointer.offset offsetBits p = 0) &&
      m.heap.contains (Pointer.object offsetBits p) &&
      (m.bytes (Pointer.object offsetBits p)).isSome)
  pure ((m.release offsetBits p).setGlobal "__CPROVER_deallocated" p)

end GotoLean.Memory
