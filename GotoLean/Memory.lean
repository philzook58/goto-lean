import GotoLean.Aggregates

/-! Little-endian object memory. Objects zero and one are null and invalid, as in CBMC;
released IDs are never reused.
An allocation's initial bit pattern comes from the ordinary declaration choice.
Invalid accesses are explicit safety checks, with their own source-site suffix. -/
namespace GotoLean

namespace Pointer

/-- CBMC stores the object ID above the byte-offset bits. -/
def object (offsetBits : Nat) (p : BitVec w) : Nat := (p >>> offsetBits).toNat

def offset (offsetBits : Nat) (p : BitVec w) : Nat := (p.setWidth offsetBits).toNat

def make (offsetBits : Nat) (object : Nat) (offset : BitVec offsetBits) : BitVec w :=
  shiftLeft (BitVec.ofNat w object) offsetBits ||| offset.setWidth w

/-- Offset arithmetic wraps within the offset field; it cannot carry into the object ID. -/
def add (offsetBits : Nat) (p : BitVec w) (bytes : Int) : BitVec w :=
  make offsetBits (object offsetBits p)
    (p.setWidth offsetBits + BitVec.ofInt offsetBits bytes)

/-- As in CBMC, ordered comparison of pointers to different objects returns false. -/
def compare (offsetBits : Nat) (inclusive : Bool) (p q : BitVec w) : Bool :=
  object offsetBits p == object offsetBits q &&
    if inclusive then BitVec.ule (p.setWidth offsetBits) (q.setWidth offsetBits)
    else BitVec.ult (p.setWidth offsetBits) (q.setWidth offsetBits)

end Pointer

/-- CBMC leaves subtraction between distinct objects unconstrained. -/
def pointerDifference (site : Site) (offsetBits width elementBytes : Nat)
    (p q : BitVec w) : Action (BitVec width) := do
  if Pointer.object offsetBits p == Pointer.object offsetBits q then
    let difference :=
      (p.setWidth offsetBits).setWidth width - (q.setWidth offsetBits).setWidth width
    if elementBytes == 1 then pure difference
    else divide site true false difference (BitVec.ofNat width elementBytes)
  else choose site width

/-- Byte arrays retain their arbitrary initial contents until overwritten.
`none` denotes a dead object, including the reserved null and invalid objects. -/
structure Memory where
  objects : Array (Option (Array (BitVec 8))) := #[none, none]
  globals : List (String × Nat) := []
  heap : List Nat := [] -- IDs allocated by malloc, including released objects
  deriving Repr, BEq, DecidableEq

namespace Memory

/-- Value-only global storage; absent entries have their GOTO symbol's initial bit pattern. -/
def getGlobal (m : Memory) (name : String) (initial : BitVec w) : BitVec w :=
  BitVec.ofNat w ((m.globals.find? (fun entry ↦ entry.1 == name)).map Prod.snd
    |>.getD initial.toNat)

def setGlobal (m : Memory) (name : String) (value : BitVec w) : Memory :=
  { m with globals := (name, value.toNat) :: m.globals.filter (fun entry ↦ entry.1 != name) }

def bytes (m : Memory) (object : Nat) : Option (Array (BitVec 8)) :=
  m.objects[object]?.getD none

def put (m : Memory) (object : Nat) (value : Array (BitVec 8)) : Memory :=
  { m with objects := m.objects.setIfInBounds object (some value) }

def readByte (m : Memory) (object offset : Nat) : Option (BitVec 8) :=
  (m.bytes object).bind (fun b => b[offset]?)

/-- Live objects have their byte extent. An unavailable extent is conservatively unconstrained. -/
def objectSize (site : Site) (offsetBits width : Nat) (m : Memory) (p : BitVec w) :
    Action (BitVec width) :=
  match m.bytes (Pointer.object offsetBits p) with
  | some b => pure (BitVec.ofNat width b.size)
  | none => choose (site ++ "; unknown object size") width

def writeByte (m : Memory) (object offset : Nat) (value : BitVec 8) : Memory :=
  match m.bytes object with
  | none => m
  | some b => m.put object (b.setIfInBounds offset value)

theorem bytes_bound (m : Memory) (object : Nat) (b : Array (BitVec 8))
    (h : m.bytes object = some b) : object < m.objects.size := by
  by_cases ho : object < m.objects.size
  · exact ho
  · have hn : m.objects[object]? = none := Array.getElem?_eq_none (by omega)
    simp [bytes, hn] at h

/-- A store into an existing object makes its new contents available at that ID. -/
theorem bytes_put (m : Memory) (object : Nat) (b : Array (BitVec 8))
    (h : object < m.objects.size) : (m.put object b).bytes object = some b := by
  simp [put, bytes, Array.getElem?_setIfInBounds_self_of_lt h]

/-- Stores preserve every other object, including its liveness and extent. -/
theorem bytes_put_other (m : Memory) (object other : Nat) (b : Array (BitVec 8))
    (h : object ≠ other) : (m.put object b).bytes other = m.bytes other := by
  simp [put, bytes, h]

/-- Reading a byte immediately after writing it returns the written value. -/
theorem readByte_writeByte (m : Memory) (object offset : Nat) (old value : BitVec 8)
    (h : m.readByte object offset = some old) :
    (m.writeByte object offset value).readByte object offset = some value := by
  unfold readByte at h ⊢
  unfold writeByte
  cases hb : m.bytes object with
  | none => simp [hb] at h
  | some b =>
    have ho := bytes_bound m object b hb
    have hi : offset < b.size := by
      simp only [hb, Option.bind_some] at h
      obtain ⟨hi, _⟩ := Array.getElem?_eq_some_iff.mp h
      exact hi
    simp [bytes_put m object _ ho, Array.getElem?_setIfInBounds_self_of_lt hi]

/-- A byte store leaves reads from a distinct object unchanged. -/
theorem readByte_writeByte_other (m : Memory) (object other offset i : Nat)
    (value : BitVec 8) (h : object ≠ other) :
    (m.writeByte object offset value).readByte other i = m.readByte other i := by
  unfold writeByte
  cases m.bytes object <;> simp [readByte, bytes_put_other, h]

/-- A byte store also preserves every other byte of the same object. -/
theorem readByte_writeByte_disjoint (m : Memory) (object offset i : Nat)
    (value : BitVec 8) (h : offset ≠ i) :
    (m.writeByte object offset value).readByte object i = m.readByte object i := by
  unfold writeByte
  cases hb : m.bytes object with
  | none => rfl
  | some b =>
    have ho := bytes_bound m object b hb
    simp [readByte, bytes_put m object _ ho, hb, h]

def unpack (value : BitVec w) : Array (BitVec 8) :=
  (List.range ((w + 7) / 8)).toArray.map (fun i => BitVec.extractLsb' (i * 8) 8 value)

def readBits (b : Array (BitVec 8)) (offset width : Nat) : BitVec width :=
  (List.range ((width + 7) / 8)).foldl
    (fun v i => v ||| shiftLeft ((b[offset + i]?.getD 0).setWidth width) (i * 8)) 0

def writeBits (b : Array (BitVec 8)) (offset : Nat) (value : BitVec w) :
    Array (BitVec 8) :=
  (List.range ((w + 7) / 8)).foldl
    (fun b i => b.setIfInBounds (offset + i) (BitVec.extractLsb' (i * 8) 8 value)) b

/-- The byte-sized case of the same load/store representation used by generated programs. -/
theorem readBits_writeBits_byte (b : Array (BitVec 8)) (offset : Nat) (value : BitVec 8)
    (h : offset < b.size) : readBits (writeBits b offset value) offset 8 = value := by
  simp [readBits, writeBits, List.range_succ, Array.getElem?_setIfInBounds_self_of_lt h]

def valid (m : Memory) (offsetBits : Nat) (p : BitVec w) (size : Nat) : Bool :=
  decide (1 < Pointer.object offsetBits p) &&
    match m.bytes (Pointer.object offsetBits p) with
    | none => false
    | some b => decide (Pointer.offset offsetBits p + size ≤ b.size)

/-- Allocate a fresh automatic object. Exhausting the finite pointer ID space fails explicitly. -/
def alloc (site : Site) (offsetBits objectBits : Nat) (m : Memory) (value : BitVec w) :
    Action (BitVec (offsetBits + objectBits) × Memory) := do
  check (site ++ "; memory allocation")
    (decide (2 ≤ m.objects.size ∧ m.objects.size < 2 ^ objectBits ∧
      (w + 7) / 8 < 2 ^ offsetBits))
  pure (Pointer.make offsetBits m.objects.size 0,
    { m with objects := m.objects.push (some (unpack value)) })

def release (m : Memory) (offsetBits : Nat) (p : BitVec w) : Memory :=
  { m with objects := m.objects.setIfInBounds (Pointer.object offsetBits p) none }

/-- Load native Lean bits after checking object lifetime and byte bounds. -/
def load (site : Site) (offsetBits width : Nat) (m : Memory) (p : BitVec w) :
    Action (BitVec width) := do
  check (site ++ "; memory read") (m.valid offsetBits p ((width + 7) / 8))
  pure (readBits ((m.bytes (Pointer.object offsetBits p)).getD #[])
    (Pointer.offset offsetBits p) width)

/-- A store updates shared bytes, so all direct accesses and aliases observe it. -/
def store (site : Site) (offsetBits : Nat) (m : Memory) (p : BitVec pw)
    (value : BitVec w) : Action Memory := do
  check (site ++ "; memory write") (m.valid offsetBits p ((w + 7) / 8))
  pure (m.put (Pointer.object offsetBits p)
    (writeBits ((m.bytes (Pointer.object offsetBits p)).getD #[])
      (Pointer.offset offsetBits p) value))

open Std.WP Lean.Order

@[spec] theorem alloc_spec (site : Site) (offsetBits objectBits : Nat) (m : Memory)
    (value : BitVec w) (Q : BitVec (offsetBits + objectBits) × Memory → Prop) :
    ⦃decide (2 ≤ m.objects.size ∧ m.objects.size < 2 ^ objectBits ∧
      (w + 7) / 8 < 2 ^ offsetBits) = true ∧
      Q (Pointer.make offsetBits m.objects.size 0,
        { m with objects := m.objects.push (some (unpack value)) })⦄
    alloc site offsetBits objectBits m value ⦃Q⦄ := ⟨id⟩

@[spec] theorem load_spec (site : Site) (offsetBits width : Nat) (m : Memory)
    (p : BitVec w) (Q : BitVec width → Prop) :
    ⦃m.valid offsetBits p ((width + 7) / 8) = true ∧
      Q (readBits ((m.bytes (Pointer.object offsetBits p)).getD #[])
        (Pointer.offset offsetBits p) width)⦄
    load site offsetBits width m p ⦃Q⦄ := ⟨id⟩

@[spec] theorem store_spec (site : Site) (offsetBits : Nat) (m : Memory)
    (p : BitVec pw) (value : BitVec w) (Q : Memory → Prop) :
    ⦃m.valid offsetBits p ((w + 7) / 8) = true ∧
      Q (m.put (Pointer.object offsetBits p)
        (writeBits ((m.bytes (Pointer.object offsetBits p)).getD #[])
          (Pointer.offset offsetBits p) value))⦄
    store site offsetBits m p value ⦃Q⦄ := ⟨id⟩

/-- Every valid byte store can be loaded back through the same pointer. -/
theorem store_load_byte (site : Site) (offsetBits : Nat) (m : Memory)
    (p : BitVec pw) (value : BitVec 8) (h : m.valid offsetBits p 1 = true) :
    (do
      let m' ← m.store site offsetBits p value
      m'.load site offsetBits 8 p).wp (fun read => read = value) := by
  cases hb : m.bytes (Pointer.object offsetBits p) with
  | none => simp [valid, hb] at h
  | some b =>
    have hv : 1 < Pointer.object offsetBits p ∧ Pointer.offset offsetBits p + 1 ≤ b.size := by
      simpa [valid, hb] using h
    have ho := bytes_bound m _ b hb
    have hi : Pointer.offset offsetBits p < b.size := by omega
    simp [store, load, Bind.bind, Action.bind, check, Action.wp, valid,
      hb, hv, bytes_put m _ _ ho, writeBits, readBits, List.range_succ,
      Array.getElem?_setIfInBounds_self_of_lt hi]

end Memory
end GotoLean
