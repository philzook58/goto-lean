import Proofs.CopyWord
import Proofs.Scan
import GotoLean.MemoryViews
import GotoLean.PointerLemmas

/-! Algorithmic annotations for the three scans in the original generated token parser. -/
namespace TokenParser
open GotoLean ParserContracts


structure Input where
  memory : Memory
  cursor : BitVec 64
  out : BitVec 64
  source : BitVec 64
  capacity : BitVec 64
  bytes : List (BitVec 8)

/-- Separate live input, output and cursor objects with sufficient readable/writable space. -/
structure Ready (input : Input) : Prop where
  inputBytes : input.memory.BytesAt 56 input.source input.bytes
  cursorValue : input.memory.ValueAt 56 input.cursor input.source
  output : input.memory.valid 56 input.out input.capacity.toNat = true
  separate : Pointer.object 56 input.source ≠ Pointer.object 56 input.out ∧
    Pointer.object 56 input.source ≠ Pointer.object 56 input.cursor ∧
    Pointer.object 56 input.out ≠ Pointer.object 56 input.cursor
  inputBound : Pointer.offset 56 input.source + input.bytes.length < 2 ^ 56
  outputBound : Pointer.offset 56 input.out + input.capacity.toNat < 2 ^ 56

def point (input : Input) (i : Nat) : BitVec 64 := Pointer.add 56 input.source (Int.ofNat i)
def length (scan : Scan bytes) : BitVec 64 := BitVec.ofNat 64 (scan.stop - scan.start)
abbrev accepted (input : Input) (scan : Scan input.bytes) : Prop :=
  0 < scan.stop - scan.start ∧ scan.stop - scan.start < input.capacity.toNat

def copiedMemory (input : Input) (scan : Scan input.bytes) : Memory :=
  copiedWord input.memory input.out (point input scan.start) (length scan)

def finalMemory (input : Input) (scan : Scan input.bytes) : Memory :=
  (copiedMemory input scan).written 56 input.cursor (point input scan.next)

/-- Success copies the word and advances the cursor; rejection changes no memory. -/
def expected (input : Input) (scan : Scan input.bytes) : BitVec 32 × Memory :=
  if accepted input scan then (1, finalMemory input scan) else (0, input.memory)

private theorem point_offset (input : Input) (ready : Ready input) (i : Nat)
    (hi : i ≤ input.bytes.length) :
    Pointer.offset 56 (point input i) = Pointer.offset 56 input.source + i :=
  Pointer.offset_add_nat _ _ (by decide) (by have := ready.inputBound; omega)

private theorem point_next (input : Input) (ready : Ready input) (i : Nat)
    (hi : i + 1 ≤ input.bytes.length) :
    Pointer.add 56 (point input i) 1 = point input (i + 1) :=
  Pointer.add_succ _ _ (by decide) (by have := ready.inputBound; omega)

private theorem input_valid (input : Input) (ready : Ready input) (i n : Nat)
    (hi : i + n ≤ input.bytes.length) : input.memory.valid 56 (point input i) n = true := by
  obtain ⟨b, hb, ho, hn⟩ := (Memory.valid_iff ..).mp ready.inputBytes.1
  apply (Memory.valid_iff ..).mpr
  refine ⟨b, ?_, ?_, ?_⟩
  · simpa [point, Pointer.object_add] using hb
  · simpa [point, Pointer.object_add] using ho
  · rw [point_offset input ready i (by omega)]
    omega

private theorem input_value (input : Input) (ready : Ready input) (m : Memory) (i : Nat)
    (hi : i < input.bytes.length)
    (same : m.bytes (Pointer.object 56 input.source) =
      input.memory.bytes (Pointer.object 56 input.source)) :
    m.ValueAt 56 (point input i) (byte input.bytes i) := by
  obtain ⟨b, hb, ho, hn⟩ := (Memory.valid_iff ..).mp (input_valid input ready i 1 (by omega))
  have hbyte := ready.inputBytes.2 i hi
  have hm : m.bytes (Pointer.object 56 (point input i)) = some b := by
    simpa only [point, Pointer.object_add] using
      same.trans (by simpa [point, Pointer.object_add] using hb)
  constructor
  · exact (Memory.valid_iff ..).mpr ⟨b, hm, ho, hn⟩
  · simp only [Memory.readByte] at hbyte
    rw [show input.memory.bytes (Pointer.object 56 input.source) = some b by
      simpa [point, Pointer.object_add] using hb] at hbyte
    simp only [Option.bind_some] at hbyte
    simp only [Memory.readBits, List.range_succ, List.range_zero, List.foldl_append,
      List.foldl_cons, List.foldl_nil, hm, Option.getD_some]
    simp only [shiftLeft_eq, BitVec.setWidth_eq]
    rw [point_offset input ready i (by omega)]
    simpa [byte, List.getElem?_eq_getElem hi] using
      congrArg (fun x ↦ x.getD 0) hbyte

private theorem space_test (b : BitVec 8) :
    (BitVec.signExtend 32 b == (32 : BitVec 32)) = (b == 32) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq]
  constructor
  · intro h
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have he := congrArg (fun x ↦ x.getLsbD i) h
    have hi32 : i < 32 := by omega
    simp only [BitVec.getLsbD_signExtend, hi, hi32, decide_true, Bool.true_and, ite_true] at he
    exact he
  · intro h
    subst b
    decide

private theorem length_test (n capacity : BitVec 64) :
    (!((!(n != (0 : BitVec 64))) || BitVec.ule capacity n)) =
      decide (0 < n.toNat ∧ n.toNat < capacity.toNat) := by
  apply Bool.eq_iff_iff.mpr
  simp [BitVec.ule, ← BitVec.toNat_inj]
  omega

private theorem length_nat (input : Input) (scan : Scan input.bytes) (ready : Ready input) :
    (length scan).toNat = scan.stop - scan.start := by
  have := scan.bounded
  have := scan.ordered
  have := ready.inputBound
  exact Nat.mod_eq_of_lt (by omega)

private theorem word_difference (input : Input) (scan : Scan input.bytes) (ready : Ready input)
    (site : Site) : pointerDifference site 56 64 1 (point input scan.stop)
      (point input scan.start) = pure (length scan) := by
  have hs : scan.start ≤ input.bytes.length := by have := scan.ordered; have := scan.bounded; omega
  have he : scan.stop ≤ input.bytes.length := by have := scan.ordered; have := scan.bounded; omega
  simp only [pointerDifference, point, Pointer.object_add, beq_self_eq_true, ite_true]
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_setWidth_of_le (by decide : 56 ≤ 64),
    BitVec.toNat_setWidth_of_le (by decide : 56 ≤ 64)]
  change ((2 ^ 64 - Pointer.offset 56 (point input scan.start) +
    Pointer.offset 56 (point input scan.stop)) % 2 ^ 64) = (length scan).toNat
  rw [point_offset input ready scan.start hs, point_offset input ready scan.stop he,
    length_nat input scan ready]
  have := scan.ordered
  have := ready.inputBound
  omega

private theorem copy_pre (input : Input) (scan : Scan input.bytes) (ready : Ready input)
    (ok : accepted input scan) :
    CopyPre input.memory input.out (point input scan.start) (length scan) input.capacity := by
  have order := scan.ordered
  have bound := scan.bounded
  have hn := length_nat input scan ready
  constructor
  · simpa [hn] using ok.2
  · rw [hn]
    exact input_valid input ready _ _ (by omega)
  · exact ready.output
  · simp [Memory.disjoint, point, Pointer.object_add, Ne.symm ready.separate.1]
  · rw [hn]
    have := ready.outputBound
    omega

private theorem copied_input (input : Input) (scan : Scan input.bytes) (ready : Ready input) :
    (copiedMemory input scan).bytes (Pointer.object 56 input.source) =
      input.memory.bytes (Pointer.object 56 input.source) := by
  unfold copiedMemory copiedWord Memory.writeByte
  split <;> simp [Memory.copied, Memory.bytes_put_other, Ne.symm ready.separate.1]

/-- The current pointer stays within the indicated half-open interval of source positions. -/
private def At (input : Input) (m : Memory) (lo hi : Nat)
    (s : v_take_word.Functions.v_take_word.Locals) : Prop :=
  s.memory = m ∧ ∃ i, lo ≤ i ∧ i < hi ∧ s.v_p = point input i

private def invariant (input : Input) (scan : Scan input.bytes) : CallerInvariant := fun (pc, s) Q ↦
  s.v_cursor = input.cursor ∧ s.v_out = input.out ∧ s.v_capacity = input.capacity ∧
    Q (.v_take_word (expected input scan)) ∧
    match pc with
    | .b0 => s.memory = input.memory
    | .b2 => At input input.memory 0 (scan.start + 1) s -- skip leading spaces
    | .b3 => At input input.memory 0 scan.start s
    | .b5 => s.memory = input.memory ∧ s.v_p = point input scan.start
    | .b8 => s.v_start = point input scan.start ∧
        At input input.memory scan.start (scan.stop + 1) s -- scan the word
    | .b9 => s.v_start = point input scan.start ∧ At input input.memory scan.start scan.stop s
    | .b11 => s.memory = input.memory ∧ s.v_start = point input scan.start ∧
        s.v_p = point input scan.stop
    | .b15 => ¬accepted input scan ∧ s.memory = input.memory
    | .b20 => accepted input scan ∧ s.memory = input.memory ∧
        s.v_start = point input scan.start ∧ s.v_p = point input scan.stop ∧ s.v_n = length scan
    | .b22 => accepted input scan ∧
        At input (copiedMemory input scan) scan.stop (scan.next + 1) s -- skip trailing spaces
    | .b23 => accepted input scan ∧ At input (copiedMemory input scan) scan.stop scan.next s
    | .b25 => accepted input scan ∧ s.memory = copiedMemory input scan ∧
        s.v_p = point input scan.next
    | .b32 => s.result = some (expected input scan).1 ∧ s.memory = (expected input scan).2

private theorem blocks (input : Input) (scan : Scan input.bytes) (ready : Ready input)
    (frame : v_take_word.Functions.v_take_word.Frame) (Q : v_take_word.Value → Prop)
    (hi : invariant input scan frame Q) :
    (v_take_word.body (.v_take_word frame)).wp
      (Transfer.wp · (annotated (invariant input scan)) Q) := by
  rcases frame with ⟨pc, s⟩
  rcases hi with ⟨hc, ho, hcap, hq, hs⟩
  have order := scan.ordered
  have bound := scan.bounded
  cases pc with
  | b0 =>
    simp only [v_take_word.body, Bind.bind, Action.wp_bind, Action.wp_pure, choose, Action.wp]
    intro choice
    rw [hc, hs, Memory.load_value _ _ _ _ _ ready.cursorValue]
    refine ⟨rfl, ho, hcap, hq, rfl, 0, by omega, by omega, ?_⟩
    exact (Pointer.add_zero input.source (by decide)).symm
  | b2 =>
    obtain ⟨hm, i, hlo, hhi, hp⟩ := hs
    simp only [v_take_word.body, Bind.bind, Action.wp_bind, hm, hp]
    rw [Memory.load_value _ _ _ _ _ (input_value input ready _ i (by omega) rfl)]
    by_cases hlt : i < scan.start
    · have hb := scan.leading i hlt
      simp only [space_test, hb, beq_self_eq_true, Bool.not_true, Bool.false_eq_true,
        ite_false, Action.wp_pure]
      exact ⟨hc, ho, hcap, hq, hm, i, hlo, hlt, hp⟩
    · have he : i = scan.start := by omega
      have hb : (byte input.bytes i == 32) = false := by
        apply Bool.eq_false_iff.mpr
        intro h
        have heq : byte input.bytes i = 32 := of_decide_eq_true h
        rw [he] at heq
        exact scan.first heq
      simp only [space_test, hb, Bool.not_false, ite_true, Action.wp_pure]
      exact ⟨hc, ho, hcap, hq, hm, he ▸ hp⟩
  | b3 =>
    obtain ⟨hm, i, hlo, hhi, hp⟩ := hs
    simp only [v_take_word.body, hp, Action.wp_pure]
    refine ⟨hc, ho, hcap, hq, hm, i + 1, by omega, by omega, ?_⟩
    simpa using point_next input ready i (by omega)
  | b5 =>
    obtain ⟨hm, hp⟩ := hs
    simp only [v_take_word.body, Bind.bind, Action.wp_bind, choose, Action.wp, Action.wp_pure]
    intro choice
    exact ⟨hc, ho, hcap, hq, hp, hm, scan.start, by omega, by omega, hp⟩
  | b8 =>
    obtain ⟨hstart, hm, i, hlo, hhi, hp⟩ := hs
    have read (site : Site) (R : BitVec 8 → Prop) := Memory.load_value site input.memory 56
      (point input i) (byte input.bytes i) (input_value input ready _ i (by omega) rfl) R
    simp only [v_take_word.body, Bind.bind, Action.wp_bind, hm, hp]
    rw [read]
    by_cases hlt : i < scan.stop
    · have hb := scan.word i hlo hlt
      have nonzero : (byte input.bytes i != (0 : BitVec 8)) = true := by simpa using hb.1
      have nonspace : (BitVec.signExtend 32 (byte input.bytes i) != (32 : BitVec 32)) = true := by
        change (!(BitVec.signExtend 32 (byte input.bytes i) == (32 : BitVec 32))) = true
        rw [space_test]
        simpa using hb.2
      simp only [nonzero, nonspace, ite_true, Bool.not_true, Bool.false_eq_true, ite_false,
        Bind.bind, Action.wp_bind, Action.wp_pure, read]
      exact ⟨hc, ho, hcap, hq, hstart, hm, i, hlo, hlt, hp⟩
    · have he : i = scan.stop := by omega
      have hb : byte input.bytes i = 0 ∨ byte input.bytes i = 32 := he ▸ scan.delimiter
      rcases hb with hb | hb <;>
        simp [hb, space_test, Bind.bind, Action.wp_bind, Action.wp_pure, read] <;>
        exact ⟨hc, ho, hcap, hq, hm, hstart, he ▸ hp⟩
  | b9 =>
    obtain ⟨hstart, hm, i, hlo, hhi, hp⟩ := hs
    simp only [v_take_word.body, hp, Action.wp_pure]
    refine ⟨hc, ho, hcap, hq, hstart, hm, i + 1, by omega, by omega, ?_⟩
    simpa using point_next input ready i (by omega)
  | b11 =>
    obtain ⟨hm, hstart, hp⟩ := hs
    simp only [v_take_word.body, Bind.bind, Action.wp_bind, choose, Action.wp, hstart, hp,
      word_difference input scan ready, Action.wp_pure]
    intro choice
    have test : (!((!(length scan != (0 : BitVec 64))) ||
        BitVec.ule s.v_capacity (length scan))) = decide (accepted input scan) := by
      rw [length_test]
      simp only [length_nat input scan ready, hcap]
    rw [test]
    simp only [decide_eq_true_eq]
    split
    · rename_i ok
      exact ⟨hc, ho, hcap, hq, ok, hm, rfl, rfl, rfl⟩
    · rename_i bad
      exact ⟨hc, ho, hcap, hq, bad, hm⟩
  | b15 =>
    obtain ⟨bad, hm⟩ := hs
    simp only [v_take_word.body, Action.wp_pure]
    refine ⟨hc, ho, hcap, hq, ?_, ?_⟩
    · simp only [expected, ite_eq_right bad]
    · simpa only [expected, ite_eq_right bad] using hm
  | b20 =>
    obtain ⟨ok, hm, hstart, hp, hn⟩ := hs
    apply copy_word_call
    · simpa only [hm, ho, hstart, hn, hcap] using copy_pre input scan ready ok
    · refine ⟨hc, ho, hcap, hq, ok, ?_, scan.stop, by omega, by omega, hp⟩
      simp only [hm, ho, hstart, hn, copiedMemory]
  | b22 =>
    obtain ⟨ok, hm, i, hlo, hhi, hp⟩ := hs
    simp only [v_take_word.body, Bind.bind, Action.wp_bind, hm, hp]
    rw [Memory.load_value _ _ _ _ _
      (input_value input ready _ i (by omega) (copied_input input scan ready))]
    by_cases hlt : i < scan.next
    · have hb := scan.trailing i hlo hlt
      simp only [space_test, hb, beq_self_eq_true, Bool.not_true, Bool.false_eq_true,
        ite_false, Action.wp_pure]
      exact ⟨hc, ho, hcap, hq, ok, hm, i, hlo, hlt, hp⟩
    · have he : i = scan.next := by omega
      have hb : (byte input.bytes i == 32) = false := by
        apply Bool.eq_false_iff.mpr
        intro h
        have heq : byte input.bytes i = 32 := of_decide_eq_true h
        rw [he] at heq
        exact scan.last heq
      simp only [space_test, hb, Bool.not_false, ite_true, Action.wp_pure]
      exact ⟨hc, ho, hcap, hq, ok, hm, he ▸ hp⟩
  | b23 =>
    obtain ⟨ok, hm, i, hlo, hhi, hp⟩ := hs
    simp only [v_take_word.body, hp, Action.wp_pure]
    refine ⟨hc, ho, hcap, hq, ok, hm, i + 1, by omega, by omega, ?_⟩
    simpa using point_next input ready i (by omega)
  | b25 =>
    obtain ⟨ok, hm, hp⟩ := hs
    have cursor_valid : (copiedMemory input scan).valid 56 input.cursor 8 = true := by
      have ext object := (copiedWord_spec _ _ _ _ _ (copy_pre input scan ready ok)).extent object
      change (copiedWord input.memory input.out (point input scan.start) (length scan)).valid
        56 input.cursor 8 = true
      rw [Memory.valid_of_extent input.memory _ ext]
      exact ready.cursorValue.1
    simp only [v_take_word.body, Bind.bind, Action.wp_bind, hm, hc, hp]
    rw [Memory.store_wp]
    refine ⟨cursor_valid, rfl, ho, hcap, hq, ?_, ?_⟩ <;>
      simp only [expected, ite_eq_left ok, finalMemory]
  | b32 =>
    obtain ⟨hr, hm⟩ := hs
    simpa [v_take_word.body, hr, hm, Transfer.wp, Action.wp_pure] using hq

/-- Safety for every finite prefix and the specified result on every normal return. -/
theorem take_word_correct (input : Input) (scan : Scan input.bytes) (ready : Ready input) :
    (v_take_word.run input.cursor input.out input.capacity input.memory).wp
      (fun result ↦ result = expected input scan) := by
  apply take_word_rule (invariant input scan) (blocks input scan ready)
  refine ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- No boundary annotations are required from the user: NUL termination computes and proves them. -/
theorem verify (input : Input) (ready : Ready input) (terminated : 0 ∈ input.bytes) :
    (v_take_word.run input.cursor input.out input.capacity input.memory).wp
      (fun result ↦ result = expected input (scan input.bytes terminated)) :=
  take_word_correct input (scan input.bytes terminated) ready

/-- The readable successful-return contract, including both changed regions and the frame. -/
structure Parsed (input : Input) (scan : Scan input.bytes)
    (result : BitVec 32 × Memory) : Prop where
  success : result.1 = 1
  cursor : result.2.ValueAt 56 input.cursor (point input scan.next)
  copied : ∀ i, i < scan.stop - scan.start →
    result.2.readByte (Pointer.object 56 input.out) (Pointer.offset 56 input.out + i) =
      input.memory.readByte (Pointer.object 56 input.source)
        (Pointer.offset 56 input.source + scan.start + i)
  terminated : result.2.readByte (Pointer.object 56 input.out)
    (Pointer.offset 56 input.out + (scan.stop - scan.start)) = some 0
  outputFrame : ∀ i, i < Pointer.offset 56 input.out ∨
    Pointer.offset 56 input.out + (scan.stop - scan.start) < i →
      result.2.readByte (Pointer.object 56 input.out) i =
        input.memory.readByte (Pointer.object 56 input.out) i
  cursorFrame : ∀ i, i < Pointer.offset 56 input.cursor ∨ Pointer.offset 56 input.cursor + 8 ≤ i →
    result.2.readByte (Pointer.object 56 input.cursor) i =
      input.memory.readByte (Pointer.object 56 input.cursor) i
  inputUnchanged : result.2.bytes (Pointer.object 56 input.source) =
    input.memory.bytes (Pointer.object 56 input.source)
  frame : ∀ object, object ≠ Pointer.object 56 input.out →
    object ≠ Pointer.object 56 input.cursor → result.2.bytes object = input.memory.bytes object

private theorem copied_other (input : Input) (scan : Scan input.bytes) (object : Nat)
    (ho : Pointer.object 56 input.out ≠ object) :
    (copiedMemory input scan).bytes object = input.memory.bytes object := by
  unfold copiedMemory copiedWord Memory.writeByte
  split <;> simp [Memory.copied, Memory.bytes_put_other, ho]

/-- On success, callers get the word, updated cursor, unchanged input and a memory frame. -/
theorem success (input : Input) (scan : Scan input.bytes) (ready : Ready input)
    (ok : accepted input scan) :
    (v_take_word.run input.cursor input.out input.capacity input.memory).wp
      (Parsed input scan) := by
  apply (v_take_word.run input.cursor input.out input.capacity input.memory).mono ?_
    (take_word_correct input scan ready)
  intro result hr
  rw [hr, expected, ite_eq_left ok]
  have copied := copiedWord_spec _ _ _ _ _ (copy_pre input scan ready ok)
  have cursor_valid : (copiedMemory input scan).valid 56 input.cursor 8 = true := by
    exact (Memory.valid_of_extent input.memory _ copied.extent 56 input.cursor 8).trans
      ready.cursorValue.1
  have reads (i : Nat) : (finalMemory input scan).readByte (Pointer.object 56 input.out) i =
      (copiedMemory input scan).readByte (Pointer.object 56 input.out) i := by
    simp [finalMemory, Memory.readByte, Memory.bytes_written_other, Ne.symm ready.separate.2.2]
  constructor
  · rfl
  · exact Memory.valueAt_written _ 56 input.cursor _ (Or.inr rfl) cursor_valid
  · intro i hi
    rw [reads]
    have h := copied.copied i (by rw [length_nat input scan ready]; exact hi)
    rw [point_offset input ready scan.start
      (by have := scan.ordered; have := scan.bounded; omega)] at h
    simpa only [copiedMemory, point, Pointer.object_add] using h
  · rw [reads, ← length_nat input scan ready]
    exact copied.terminated
  · intro i hi
    rw [reads]
    exact copied.frame _ i (by rw [length_nat input scan ready]; omega)
  · intro i hi
    rw [finalMemory, Memory.readByte_written_frame _ _ _ _ cursor_valid _ i (Or.inr hi)]
    simp only [Memory.readByte, copied_other input scan _ ready.separate.2.2]
  · rw [finalMemory, Memory.bytes_written_other _ _ _ _ _ (Ne.symm ready.separate.2.1)]
    exact copied_input input scan ready
  · intro object ho hc
    rw [finalMemory, Memory.bytes_written_other _ _ _ _ _ (Ne.symm hc)]
    exact copied_other input scan object (Ne.symm ho)

theorem rejected (input : Input) (scan : Scan input.bytes) (ready : Ready input)
    (bad : ¬accepted input scan) :
    (v_take_word.run input.cursor input.out input.capacity input.memory).wp
      (fun result ↦ result = (0, input.memory)) := by
  simpa only [expected, ite_eq_right bad] using take_word_correct input scan ready


end TokenParser
