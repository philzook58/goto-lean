import Spec.Array
import Spec.CheckedFill
import GotoLean.Audit

/-! Twenty named shapes per algorithm. These are admitted-execution witnesses, not coverage scores.
The premise theorem separately checks the memory/length/pivot assumptions of the array contracts.
Lower-bound uses sorted cases; the other six algorithms receive the original arrays. -/
namespace ArrayExamples.Cases
open GotoLean

structure Case where
  name : String
  xs : List Int
  key : Int
  pivot : Nat
  deriving Repr

def cases : List Case := [
  ⟨"empty-zero", [], 0, 0⟩, ⟨"singleton-negative", [-1], -2147483648, 0⟩,
  ⟨"singleton-zero", [0], 0, 0⟩, ⟨"singleton-one", [1], -1, 1⟩,
  ⟨"singleton-min", [-2147483648], 2147483647, 0⟩,
  ⟨"singleton-max", [2147483647], -2147483648, 1⟩,
  ⟨"pair-sorted", [1, 2], 1, 0⟩, ⟨"pair-reversed", [2, 1], 2, 1⟩,
  ⟨"pair-duplicates", [1, 1], 0, 2⟩,
  ⟨"pair-extrema", [2147483647, -2147483648], 2147483647, 1⟩,
  ⟨"triple-sorted", [-1, 0, 1], 0, 1⟩, ⟨"triple-reversed", [1, 0, -1], 2, 2⟩,
  ⟨"triple-equal", [-1, -1, -1], -1, 3⟩,
  ⟨"triple-duplicates", [0, 1, 0], 0, 0⟩,
  ⟨"four-sorted", [-2, -1, 0, 1], 2, 0⟩, ⟨"four-reversed", [3, 2, 1, 0], 1, 4⟩,
  ⟨"four-duplicates", [1, 0, 1, 0], 0, 2⟩,
  ⟨"four-equal", [0, 0, 0, 0], 2147483647, 1⟩,
  ⟨"four-extrema", [-2147483648, 2147483647, -2147483648, 2147483647], 0, 3⟩,
  ⟨"four-mixed", [7, -3, 2, -1], -3, 2⟩]

def sortedCases : List Case := [
  ⟨"empty-zero", [], 0, 0⟩, ⟨"empty-min", [], -2147483648, 0⟩,
  ⟨"singleton-hit", [0], 0, 0⟩, ⟨"singleton-before", [1], -1, 0⟩,
  ⟨"singleton-after", [-2147483648], 2147483647, 0⟩,
  ⟨"singleton-max", [2147483647], -2147483648, 0⟩,
  ⟨"pair-first", [1, 2], 1, 0⟩, ⟨"pair-last", [1, 2], 2, 0⟩,
  ⟨"pair-duplicates", [1, 1], 0, 0⟩,
  ⟨"pair-extrema", [-2147483648, 2147483647], 2147483647, 0⟩,
  ⟨"triple-middle", [-1, 0, 1], 0, 0⟩, ⟨"triple-after", [-1, 0, 1], 2, 0⟩,
  ⟨"triple-equal", [-1, -1, -1], -1, 0⟩,
  ⟨"triple-duplicates", [0, 0, 1], 0, 0⟩,
  ⟨"four-after", [-2, -1, 0, 1], 2, 0⟩, ⟨"four-middle", [0, 1, 2, 3], 1, 0⟩,
  ⟨"four-duplicates", [0, 0, 1, 1], 0, 0⟩,
  ⟨"four-equal", [0, 0, 0, 0], 2147483647, 0⟩,
  ⟨"four-extrema", [-2147483648, -2147483648, 2147483647, 2147483647], 0, 0⟩,
  ⟨"four-negative", [-3, -1, 2, 7], -3, 0⟩]

def pointer : BitVec 64 := Pointer.make 56 2 4
def bits (x : Int) := BitVec.ofInt 32 x
private def bytes (c : Case) : Array (BitVec 8) :=
  #[165, 165, 165, 165] ++ (c.xs.flatMap (fun x ↦ (Memory.unpack (bits x)).toList)).toArray ++
    #[90, 90, 90, 90]
def memory (c : Case) : Memory := { objects := #[none, none, some (bytes c)] }
def values (c : Case) : Values := fun i ↦ bits (c.xs[i]?.getD 0)
def length (c : Case) : BitVec 32 := .ofNat 32 c.xs.length
def choices := List.replicate 200 0

private instance (m : Memory) (p : BitVec 64) (value : BitVec 32) :
    Decidable (m.ValueAt 56 p value) :=
  inferInstanceAs (Decidable (m.valid 56 p 4 = true ∧
    Memory.readBits ((m.bytes (Pointer.object 56 p)).getD #[]) (Pointer.offset 56 p) 32 = value))

-- Finite checks avoid unfolding an execution to establish the specification's premises.
private theorem finitePremises : ∀ c ∈ cases ++ sortedCases,
    (List.range c.xs.length).all (fun i ↦ decide (
      (memory c).ValueAt 56 (address pointer i) (values c i))) = true ∧
    (bytes c).size < 2^64 ∧
    Pointer.offset 56 pointer + 4*c.xs.length < 2^56 ∧
    c.pivot ≤ c.xs.length := by
  have checked : (cases ++ sortedCases).all (fun c ↦ decide (
      (List.range c.xs.length).all (fun i ↦ decide (
        (memory c).ValueAt 56 (address pointer i) (values c i))) = true ∧
      (bytes c).size < 2^64 ∧ Pointer.offset 56 pointer + 4*c.xs.length < 2^56 ∧
      c.pivot ≤ c.xs.length)) = true := by
    simp only [List.all_append, cases, sortedCases, List.all_cons, List.all_nil,
      Bool.and_eq_true, and_true]
    repeat' apply And.intro
    all_goals decide +kernel
  simpa only [List.all_eq_true, decide_eq_true_eq] using checked

/-- Every listed array satisfies readability, nonwrapping, live-object and pivot premises. -/
theorem premises : ∀ c ∈ cases ++ sortedCases,
    WordsAt (memory c) pointer c.xs.length (values c) ∧
    Pointer.offset 56 pointer + 4*c.xs.length < 2^56 ∧
    CheckedSpec.ObjectState (memory c) pointer ∧ c.pivot ≤ c.xs.length := by
  intro c hc
  obtain ⟨readable, sizeFits, nowrap, pivot⟩ := finitePremises c hc
  simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq] at readable
  refine ⟨readable, nowrap, ?_, pivot⟩
  constructor
  · intro b hb
    change some (bytes c) = some b at hb
    cases Option.some.inj hb
    exact sizeFits
  · simp [memory, Memory.getGlobal, pointer, Pointer.object, Pointer.make, shiftLeft_eq]
  · simp [memory, Memory.getGlobal, pointer, Pointer.object, Pointer.make, shiftLeft_eq]

/-- The lower-bound inputs additionally satisfy the sortedness premise. -/
theorem sorted : ∀ c ∈ sortedCases, Increasing (values c) c.xs.length := by
  have checked : sortedCases.all (fun c ↦
      (List.range c.xs.length).all (fun i ↦ (List.range c.xs.length).all (fun j ↦
        decide (i ≤ j → (values c i).toInt ≤ (values c j).toInt)))) = true := by
    simp only [sortedCases, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
    repeat' apply And.intro
    all_goals decide +kernel
  simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq] at checked
  intro c hc i j hij hj
  exact checked c hc i (by omega) j hj hij

/-- The human-readable lengths and pivots survive conversion to C's 32-bit size type. -/
theorem sizes : ∀ c ∈ cases ++ sortedCases,
    (length c).toNat = c.xs.length ∧ (BitVec.ofNat 32 c.pivot).toNat = c.pivot := by
  have checked : (cases ++ sortedCases).all (fun c ↦ decide (
    (length c).toNat = c.xs.length ∧ (BitVec.ofNat 32 c.pivot).toNat = c.pivot)) = true := by
    decide +kernel
  simpa only [List.all_eq_true, decide_eq_true_eq] using checked

#guard cases.length == 20 && (cases.map Case.xs).eraseDups.length == 20
#guard sortedCases.length == 20 &&
  (sortedCases.map (fun c ↦ (c.xs, c.key))).eraseDups.length == 20
#check_axioms sizes
#check_axioms premises
#check_axioms sorted
end ArrayExamples.Cases

-- Export these same rows to the existing native/Lean comparison runners.
def main (args : List String) : IO Unit := do
  let rows := if args == ["sorted"] then ArrayExamples.Cases.sortedCases
    else ArrayExamples.Cases.cases
  for c in rows do
    let fields := [(c.xs.length : Int), c.key, (c.pivot : Int)] ++ c.xs
    IO.println (c.name ++ "|" ++ " ".intercalate (fields.map toString))
