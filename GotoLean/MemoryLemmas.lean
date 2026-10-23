import GotoLean.Library

/-! Byte-level specifications of the executable memory operations. -/
namespace GotoLean.Memory

private theorem copy_prefix (dst src : Array (BitVec 8)) (offset n : Nat)
    (hn : n ≤ src.size) (hd : offset + n ≤ dst.size) :
    let result := (List.range n).foldl
      (fun b i ↦ b.setIfInBounds (offset + i) src[i]!) dst
    result.size = dst.size ∧ ∀ i, result[i]? =
      if offset ≤ i ∧ i < offset + n then src[i - offset]? else dst[i]? := by
  induction n with
  | zero =>
    constructor
    · rfl
    · intro i
      simp only [List.range_zero, List.foldl_nil, Nat.add_zero]
      rw [ite_eq_right (by omega : ¬(offset ≤ i ∧ i < offset))]
  | succ n ih =>
    obtain ⟨hs, hr⟩ := ih (by omega) (by omega)
    simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    constructor
    · simpa using hs
    · intro i
      by_cases hi : offset + n = i
      · subst i
        rw [Array.getElem?_setIfInBounds_self_of_lt (by omega)]
        simp [show offset ≤ offset + n ∧ offset + n < offset + (n + 1) by omega,
          show offset + n - offset = n by omega, getElem!_pos src n (by omega),
          Array.getElem?_eq_getElem (xs := src) (i := n) (by omega)]
      · rw [Array.getElem?_setIfInBounds_ne hi, hr]
        have : (offset ≤ i ∧ i < offset + n) ↔
            (offset ≤ i ∧ i < offset + (n + 1)) := by omega
        simp only [this]

/-- Copying a slice preserves the destination's extent. -/
theorem size_copyBytes (dst src : Array (BitVec 8)) (offset : Nat)
    (h : offset + src.size ≤ dst.size) : (copyBytes dst offset src).size = dst.size :=
  (copy_prefix dst src offset src.size (by omega) h).1

/-- Copied bytes come from the snapshot; every byte outside the slice is unchanged. -/
theorem getElem?_copyBytes (dst src : Array (BitVec 8)) (offset i : Nat)
    (h : offset + src.size ≤ dst.size) :
    (copyBytes dst offset src)[i]? =
      if offset ≤ i ∧ i < offset + src.size then src[i - offset]? else dst[i]? :=
  (copy_prefix dst src offset src.size (by omega) h).2 i

/-- A checked pointer names a live object and a sufficiently large byte range. -/
theorem valid_iff (m : Memory) (bits : Nat) (p : BitVec w) (n : Nat) :
    m.valid bits p n = true ↔ ∃ b, m.bytes (Pointer.object bits p) = some b ∧
      1 < Pointer.object bits p ∧ Pointer.offset bits p + n ≤ b.size := by
  cases hb : m.bytes (Pointer.object bits p) <;> simp [valid, hb]

theorem valid_mono (m : Memory) (bits : Nat) (p : BitVec w) (n k : Nat) (h : k ≤ n)
    (hv : m.valid bits p n = true) : m.valid bits p k = true := by
  obtain ⟨b, hb, ho, hn⟩ := (valid_iff ..).mp hv
  exact (valid_iff ..).mpr ⟨b, hb, ho, by omega⟩

/-- Snapshot copying preserves the extent and liveness of every object. -/
theorem copied_extent (m : Memory) (bits : Nat) (dst src : BitVec w) (n object : Nat)
    (hs : m.valid bits src n = true) (hd : m.valid bits dst n = true) :
    ((m.copied bits dst src n).bytes object).map Array.size =
      (m.bytes object).map Array.size := by
  obtain ⟨a, ha, _, hsa⟩ := (valid_iff ..).mp hs
  obtain ⟨b, hb, _, hdb⟩ := (valid_iff ..).mp hd
  by_cases ho : Pointer.object bits dst = object
  · subst object
    simp only [copied, ha, hb, Option.getD_some, bytes_put m _ _ (bytes_bound m _ b hb),
      Option.map_some]
    rw [size_copyBytes]
    simp only [Array.size_extract]
    omega
  · simp [copied, bytes_put_other, ho]

/-- The byte-level copy contract includes a frame condition for every untouched byte. -/
theorem readByte_copied (m : Memory) (bits : Nat) (dst src : BitVec w) (n object i : Nat)
    (hs : m.valid bits src n = true) (hd : m.valid bits dst n = true) :
    (m.copied bits dst src n).readByte object i =
      if object = Pointer.object bits dst ∧ Pointer.offset bits dst ≤ i ∧
          i < Pointer.offset bits dst + n then
        m.readByte (Pointer.object bits src)
          (Pointer.offset bits src + (i - Pointer.offset bits dst))
      else m.readByte object i := by
  obtain ⟨a, ha, _, hsa⟩ := (valid_iff ..).mp hs
  obtain ⟨b, hb, _, hdb⟩ := (valid_iff ..).mp hd
  by_cases ho : object = Pointer.object bits dst
  · subst object
    have he : (a.extract (Pointer.offset bits src) (Pointer.offset bits src + n)).size = n := by
      simp only [Array.size_extract]; omega
    simp only [copied, ha, hb, Option.getD_some, readByte,
      bytes_put m _ _ (bytes_bound m _ b hb), Option.bind_some, true_and]
    rw [getElem?_copyBytes _ _ _ _ (by rw [he]; exact hdb), he]
    split
    · rename_i hi
      rw [Array.getElem?_extract]
      simp only [show min (Pointer.offset bits src + n) a.size =
          Pointer.offset bits src + n by omega]
      rw [ite_eq_left (by omega)]
    · rfl
  · have hne : Pointer.object bits dst ≠ object := Ne.symm ho
    simp [copied, readByte, bytes_put_other, hne, ho]

/-- A byte store preserves all object extents, including out-of-bounds stores. -/
theorem writeByte_extent (m : Memory) (object offset : Nat) (value : BitVec 8) (other : Nat) :
    ((m.writeByte object offset value).bytes other).map Array.size =
      (m.bytes other).map Array.size := by
  unfold writeByte
  cases hb : m.bytes object with
  | none => rfl
  | some b =>
    by_cases ho : object = other
    · subst other
      simp [bytes_put m _ _ (bytes_bound m _ b hb), hb]
    · simp [bytes_put_other, ho]

/-- Access checks depend only on object liveness and extent. -/
theorem valid_of_extent (m m' : Memory)
    (h : ∀ object, (m'.bytes object).map Array.size = (m.bytes object).map Array.size)
    (bits : Nat) (p : BitVec w) (n : Nat) : m'.valid bits p n = m.valid bits p n := by
  have he := h (Pointer.object bits p)
  cases hb : m.bytes (Pointer.object bits p) <;>
    cases hb' : m'.bytes (Pointer.object bits p) <;>
    simp [hb, hb'] at he <;> simp [valid, hb, hb', he]

/-- The executable eight-bit store is exactly the ordinary byte update after its safety check. -/
theorem store_byte_wp (site : Site) (bits : Nat) (m : Memory) (p : BitVec w)
    (value : BitVec 8) (Q : Memory → Prop) :
    (m.store site bits p value).wp Q ↔ m.valid bits p 1 = true ∧
      Q (m.writeByte (Pointer.object bits p) (Pointer.offset bits p) value) := by
  cases hb : m.bytes (Pointer.object bits p) <;>
    simp [store, valid, hb, writeByte, writeBits, List.range_succ,
      Bind.bind, Action.bind, check, Action.wp]

end GotoLean.Memory
