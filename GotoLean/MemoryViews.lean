import GotoLean.MemoryLemmas

/-! Small proof views of ordinary values and byte sequences in executable memory. -/
namespace GotoLean.Memory

/-- A readable pointer containing a particular machine value. -/
def ValueAt (m : Memory) (bits : Nat) (p : BitVec pw) (value : BitVec w) : Prop :=
  m.valid bits p ((w + 7) / 8) = true ∧
    readBits ((m.bytes (Pointer.object bits p)).getD #[]) (Pointer.offset bits p) w = value

/-- A readable byte sequence, starting at a pointer. -/
def BytesAt (m : Memory) (bits : Nat) (p : BitVec pw) (bytes : List (BitVec 8)) : Prop :=
  m.valid bits p bytes.length = true ∧ ∀ i (hi : i < bytes.length),
    m.readByte (Pointer.object bits p) (Pointer.offset bits p + i) = some bytes[i]

theorem load_value (site : Site) (m : Memory) (bits : Nat) (p : BitVec pw)
    (value : BitVec w) (h : m.ValueAt bits p value) (Q : BitVec w → Prop) :
    (m.load site bits w p).wp Q ↔ Q value := by
  simp [load, Bind.bind, Action.wp_bind, check, Action.wp, Action.wp_pure, h.1, h.2]

/-- The pure memory update performed by a checked store. -/
def written (m : Memory) (bits : Nat) (p : BitVec pw) (value : BitVec w) : Memory :=
  m.put (Pointer.object bits p) (writeBits ((m.bytes (Pointer.object bits p)).getD #[])
    (Pointer.offset bits p) value)

theorem store_wp (site : Site) (m : Memory) (bits : Nat) (p : BitVec pw)
    (value : BitVec w) (Q : Memory → Prop) :
    (m.store site bits p value).wp Q ↔
      m.valid bits p ((w + 7) / 8) = true ∧ Q (m.written bits p value) := Iff.rfl

theorem size_writeBits (b : Array (BitVec 8)) (offset : Nat) (value : BitVec w) :
    (writeBits b offset value).size = b.size := by
  unfold writeBits
  generalize List.range ((w + 7) / 8) = indices
  induction indices generalizing b with
  | nil => rfl
  | cons i rest ih => simpa using ih (b.setIfInBounds (offset + i) _)

/-- Every byte outside a stored value's byte range is unchanged. -/
theorem getElem?_writeBits_frame (b : Array (BitVec 8)) (offset : Nat) (value : BitVec w)
    (i : Nat) (outside : i < offset ∨ offset + (w + 7) / 8 ≤ i) :
    (writeBits b offset value)[i]? = b[i]? := by
  have unchanged (n : Nat) (hn : i < offset ∨ offset + n ≤ i) :
      ((List.range n).foldl
        (fun a j ↦ a.setIfInBounds (offset + j) (BitVec.extractLsb' (j * 8) 8 value)) b)[i]? =
        b[i]? := by
    induction n with
    | zero => rfl
    | succ n ih =>
      simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      rw [Array.getElem?_setIfInBounds_ne (by omega)]
      exact ih (by omega)
  exact unchanged _ outside

/-- Native 32/64-bit values round-trip through the existing little-endian byte encoding. -/
theorem readBits_writeBits_word (b : Array (BitVec 8)) (offset : Nat) (value : BitVec w)
    (word : w = 32 ∨ w = 64) (h : offset + (w + 7) / 8 ≤ b.size) :
    readBits (writeBits b offset value) offset w = value := by
  rcases word with rfl | rfl
  all_goals
    simp only [readBits, writeBits, List.range_succ, List.range_zero, List.foldl_append,
      List.foldl_cons, List.foldl_nil, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMul,
      Array.getElem?_setIfInBounds, shiftLeft_eq]
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth]
    grind

theorem written_extent (m : Memory) (bits : Nat) (p : BitVec pw) (value : BitVec w)
    (h : m.valid bits p ((w + 7) / 8) = true) (object : Nat) :
    ((m.written bits p value).bytes object).map Array.size = (m.bytes object).map Array.size := by
  obtain ⟨b, hb, _, _⟩ := (valid_iff ..).mp h
  by_cases ho : Pointer.object bits p = object
  · subst object
    simp [written, hb, bytes_put m _ _ (bytes_bound m _ b hb), size_writeBits]
  · simp [written, bytes_put_other, ho]

theorem bytes_written_other (m : Memory) (bits : Nat) (p : BitVec pw) (value : BitVec w)
    (object : Nat) (h : Pointer.object bits p ≠ object) :
    (m.written bits p value).bytes object = m.bytes object :=
  bytes_put_other m _ _ _ h

theorem readByte_written_frame (m : Memory) (bits : Nat) (p : BitVec pw) (value : BitVec w)
    (valid : m.valid bits p ((w + 7) / 8) = true) (object i : Nat)
    (outside : object ≠ Pointer.object bits p ∨ i < Pointer.offset bits p ∨
      Pointer.offset bits p + (w + 7) / 8 ≤ i) :
    (m.written bits p value).readByte object i = m.readByte object i := by
  by_cases ho : object = Pointer.object bits p
  · subst object
    obtain ⟨b, hb, _, _⟩ := (valid_iff ..).mp valid
    simp only [written, readByte, bytes_put m _ _ (bytes_bound m _ b hb),
      hb, Option.getD_some, Option.bind_some]
    exact getElem?_writeBits_frame b _ value i (by omega)
  · simp [readByte, bytes_written_other, Ne.symm ho]

theorem valueAt_written (m : Memory) (bits : Nat) (p : BitVec pw) (value : BitVec w)
    (word : w = 32 ∨ w = 64) (h : m.valid bits p ((w + 7) / 8) = true) :
    (m.written bits p value).ValueAt bits p value := by
  obtain ⟨b, hb, ho, hn⟩ := (valid_iff ..).mp h
  constructor
  · rw [valid_of_extent m _ (written_extent m bits p value h)]
    exact h
  · simp only [written, hb, Option.getD_some, bytes_put m _ _ (bytes_bound m _ b hb)]
    exact readBits_writeBits_word b _ value word hn


private theorem readByte_default (m : Memory) (object offset : Nat) :
    m.readByte object offset = ((m.bytes object).getD #[])[offset]? := by
  cases h : m.bytes object <;> simp [readByte, h]

private theorem readBits_eq_of_readByte (m m' : Memory) (object offset width : Nat)
    (h : ∀ i, i < (width + 7) / 8 →
      m'.readByte object (offset + i) = m.readByte object (offset + i)) :
    readBits ((m'.bytes object).getD #[]) offset width =
      readBits ((m.bytes object).getD #[]) offset width := by
  have byte (i : Nat) (hi : i < (width + 7) / 8) :
      ((m'.bytes object).getD #[])[offset + i]? =
        ((m.bytes object).getD #[])[offset + i]? := by
    simpa only [readByte_default] using h i hi
  have fold (indices : List Nat) (hi : ∀ i ∈ indices, i < (width + 7) / 8)
      (a : BitVec width) :
      indices.foldl (fun v i ↦ v ||| shiftLeft
        ((((m'.bytes object).getD #[])[offset + i]?.getD 0).setWidth width) (i*8)) a =
      indices.foldl (fun v i ↦ v ||| shiftLeft
        ((((m.bytes object).getD #[])[offset + i]?.getD 0).setWidth width) (i*8)) a := by
    induction indices generalizing a with
    | nil => rfl
    | cons i rest ih =>
      simp only [List.foldl_cons, byte i (hi i (by simp))]
      exact ih (fun j hj ↦ hi j (by simp [hj])) _
  exact fold _ (fun i hi ↦ List.mem_range.mp hi) _

/-- A disjoint checked store preserves a readable word and its value. -/
theorem valueAt_written_disjoint (m : Memory) (bits : Nat) (p q : BitVec pw)
    (value : BitVec w) (expected : BitVec rw)
    (write : m.valid bits p ((w + 7) / 8) = true)
    (read : m.ValueAt bits q expected)
    (apart : Pointer.object bits q ≠ Pointer.object bits p ∨
      Pointer.offset bits q + (rw + 7) / 8 ≤ Pointer.offset bits p ∨
      Pointer.offset bits p + (w + 7) / 8 ≤ Pointer.offset bits q) :
    (m.written bits p value).ValueAt bits q expected := by
  constructor
  · rw [valid_of_extent m _ (written_extent m bits p value write)]
    exact read.1
  · rw [readBits_eq_of_readByte m _ _ _ _]
    · exact read.2
    · intro i hi
      apply readByte_written_frame _ _ _ _ write
      rcases apart with ho | h | h
      · exact Or.inl ho
      · exact Or.inr (Or.inl (by omega))
      · exact Or.inr (Or.inr (by omega))

end GotoLean.Memory
