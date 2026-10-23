import Generated.Abs
import Generated.Index
import Generated.Divide
import Generated.Shift
import Generated.Add
import GotoLean.Termination

/-! The postcondition is `True` because the functional assertions are already in the C.
`finishes` still requires every translated `check` to succeed, including CBMC's safety checks.
C assumptions restrict the admitted inputs; a rejected assumption is not a returned result. -/
namespace CheckExamples
open GotoLean

/-- All source and instrumented checks hold, under the assumptions written in `checks.c`. -/
theorem absolute (x : BitVec 32) :
    finishes v_checked_abs.step 1 (v_checked_abs.initial x) (fun _ ↦ True) := by
  simp [finishes, v_checked_abs.step, v_checked_abs.initial, Bind.bind,
    Action.wp_bind, assume, choose, check, Action.wp, BitVec.slt, BitVec.sle]
  intro allowed
  have minimum : x ≠ BitVec.intMin 32 := by
    change x ≠ 2147483648#32
    exact allowed
  simp only [allowed, not_false_eq_true, or_true, true_and]
  split
  · rw [BitVec.toInt_neg_of_ne_intMin minimum]
    omega
  · omega

/-- Both division safety checks and the C assertion hold for every admitted argument pair. -/
theorem division (x divisor : BitVec 32) :
    finishes v_checked_divide.step 1 (v_checked_divide.initial x divisor) (fun _ ↦ True) := by
  simp [finishes, v_checked_divide.step, v_checked_divide.initial, Bind.bind,
    Action.wp_bind, assume, choose, check, Action.wp, divide]
  intro nonzero noOverflow
  refine ⟨nonzero, noOverflow, ?_⟩
  simp only [nonzero, ↓reduceIte, Action.wp_pure]
  by_cases one : divisor = 1#32
  · right
    rw [one, BitVec.sdiv_one]
  · exact Or.inl one

/-- The inserted bounds check and the C assertion hold for every admitted array index. -/
theorem indexing (i : BitVec 32) :
    finishes v_checked_index.step 1 (v_checked_index.initial i) (fun _ ↦ True) := by
  simp only [finishes, v_checked_index.step, v_checked_index.initial, Bind.bind,
    Action.wp_bind, assume, choose, check, Action.wp]
  intro initialArray allowed initialResult
  have bound : i.toNat < 4 := by simpa [BitVec.ult] using allowed
  have index : (i.setWidth 64).toInt = Int.ofNat i.toNat := by
    rw [BitVec.toInt_eq_toNat_of_lt (by simp; omega)]
    simp only [BitVec.toNat_setWidth, Int.ofNat_eq_natCast]
    omega
  have cases : i.toNat = 0 ∨ i.toNat = 1 ∨ i.toNat = 2 ∨ i.toNat = 3 := by omega
  rcases cases with h | h | h | h <;>
    simp [BitVec.sle, index, h, arrayRead, BitVec.slt, shiftLeft_eq]

/-- The inserted shift-distance check and the C identity assertion hold for admitted distances. -/
theorem shifting (x distance : BitVec 32) :
    finishes v_checked_shift.step 1 (v_checked_shift.initial x distance) (fun _ ↦ True) := by
  simp [finishes, v_checked_shift.step, v_checked_shift.initial, Bind.bind,
    Action.wp_bind, assume, choose, check, Action.wp, BitVec.ult, BitVec.ule]
  intro bound
  refine ⟨by omega, ?_⟩
  by_cases zero : distance = 0#32
  · right
    simp [zero]
  · exact Or.inl zero

/-- Native Lean overflow arithmetic discharges CBMC's `overflow-+` predicate. -/
theorem addition (x : BitVec 32) :
    finishes v_checked_add.step 1 (v_checked_add.initial x) (fun _ ↦ True) := by
  simp only [finishes, v_checked_add.step, v_checked_add.initial, Bind.bind,
    Action.wp_bind, assume, choose, check, Action.wp]
  intro allowed choice
  have bound : x.toInt < 2147483647 := by simpa [BitVec.slt] using allowed
  have safe : BitVec.saddOverflow x 1#32 = false := by
    have lower := BitVec.le_toInt x
    simp [BitVec.saddOverflow]
    simp at lower
    omega
  simp only [Action.wp_pure, Sum.elim, and_true]
  constructor
  · simp [safe]
  · simp only [BitVec.slt, decide_eq_true_eq]
    rw [BitVec.toInt_add_of_not_saddOverflow (by simp [safe])]
    simp
    omega

end CheckExamples
