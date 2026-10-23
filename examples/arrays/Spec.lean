import Generated
import Spec.Array
import GotoLean.Termination
import Init.Data.Array.Perm

/-!
Review these claims alongside the C files in `upstream/`. No loop invariants or proof tactics
appear here. `Verified.lean` proves every claim below from the implementation proofs.

Common vocabulary:
* `base` is a modeled 64-bit pointer: an 8-bit object ID and a 56-bit byte offset.
* `length` and `pivot` are unsigned 32-bit sizes; array values and keys are signed 32-bit ints.
* `xs i` is the original bit pattern at index `i`; only indices below `n` matter.
* `WordsAt before base n xs` means all `n` elements are readable with those contents.
* `Increasing xs n` means signed, nondecreasing order, allowing equal adjacent values.
* `Frame before after base n` means the final bytes outside these `n` elements equal the
  original bytes. This is a final-state property, not a trace-level prohibition on writes.
* `TerminatesWith` requires a finite block bound: all feasible choices are safe and return
  a result satisfying the postcondition. Safety concerns checks in the generated Lean model.

The claims concern the actual generated interpreter entry points below. The C→CBMC→Lean
translation and the fidelity of the executable memory model are not themselves proved here.
The source snapshot, ABI and source locations are recorded with the generated code.
-/
namespace ArrayExamples.Spec
open GotoLean

/-- Completion and its result, without exposing an implementation-specific block count. -/
def TerminatesWith (step : Step σ α) (start : σ) (post : α → Prop) : Prop :=
  ∃ blocks, finishes step blocks start post

/-- The array extent fits in the modeled pointer's byte-offset field. -/
def NoWrap (base : BitVec 64) (n : Nat) : Prop := Pointer.offset 56 base + 4*n < 2^56

/-- Finite contents used by Lean's standard permutation relation. -/
def contents (xs : Values) (n : Nat) : Array (BitVec 32) := Array.ofFn (fun i : Fin n ↦ xs i)

/-- `upstream/lower_bound.c`: in a sorted array, return the first index whose value is ≥ key,
or `n` if none exists. The complete memory is unchanged. -/
def lower_bound : Prop :=
  ∀ (base : BitVec 64) (length key : BitVec 32) (before : Memory) (xs : Values),
    let n := length.toNat
    WordsAt before base n xs → Increasing xs n →
    TerminatesWith v_lower_bound.step (v_lower_bound.initial base length key before)
      (fun (result, after) ↦
        result.toNat ≤ n ∧
        (∀ i, i < result.toNat → (xs i).toInt < key.toInt) ∧
        (∀ i, result.toNat ≤ i → i < n → key.toInt ≤ (xs i).toInt) ∧
        after = before)

/-- `upstream/reverse.c`: each final element `i` equals original element `n-1-i`.
Every byte outside the array is unchanged. -/
def reverse : Prop :=
  ∀ (base : BitVec 64) (length : BitVec 32) (before : Memory) (xs : Values),
    let n := length.toNat
    WordsAt before base n xs → NoWrap base n →
    TerminatesWith v_reverse.step (v_reverse.initial base length before)
      (fun (_, after) ↦
        WordsAt after base n (fun i ↦ xs (n-1-i)) ∧ Frame before after base n)

/-- `upstream/fill.c`: every final element equals `value`.
Every byte outside the array is unchanged. -/
def fill : Prop :=
  ∀ (base : BitVec 64) (length value : BitVec 32) (before : Memory) (xs : Values),
    let n := length.toNat
    WordsAt before base n xs → NoWrap base n →
    TerminatesWith v_fill.step (v_fill.initial base length value before)
      (fun (_, after) ↦ WordsAt after base n (fun _ ↦ value) ∧ Frame before after base n)

/-- `upstream/find.c`: return the first index equal to `key`, or `n` if absent.
The complete memory is unchanged; no sortedness assumption is needed. -/
def find : Prop :=
  ∀ (base : BitVec 64) (length key : BitVec 32) (before : Memory) (xs : Values),
    let n := length.toNat
    WordsAt before base n xs →
    TerminatesWith v_find.step (v_find.initial base length key before)
      (fun (result, after) ↦
        result.toNat ≤ n ∧
        (∀ i, i < result.toNat → xs i ≠ key) ∧
        (result.toNat < n → xs result.toNat = key) ∧ after = before)

/-- `upstream/is_sorted_until.c`: return the length of the longest sorted prefix.
If this is less than `n`, adding the next element breaks sortedness. Memory is unchanged. -/
def is_sorted_until : Prop :=
  ∀ (base : BitVec 64) (length : BitVec 32) (before : Memory) (xs : Values),
    let n := length.toNat
    WordsAt before base n xs →
    TerminatesWith v_is_sorted_until.step (v_is_sorted_until.initial base length before)
      (fun (result, after) ↦
        result.toNat ≤ n ∧ Increasing xs result.toNat ∧
        (result.toNat < n → ¬ Increasing xs (result.toNat+1)) ∧ after = before)

/-- `upstream/rotate.c`: rotate left by `pivot` elements and return `length-pivot`.
Both endpoint pivots are allowed. Every byte outside the array is unchanged. -/
def rotate : Prop :=
  ∀ (base : BitVec 64) (pivot length : BitVec 32) (before : Memory) (xs : Values),
    let n := length.toNat
    let k := pivot.toNat
    k ≤ n → WordsAt before base n xs → NoWrap base n →
    TerminatesWith v_rotate.step (v_rotate.initial base pivot length before)
      (fun (result, after) ↦
        result = length-pivot ∧
        WordsAt after base n (fun i ↦ if i < n-k then xs (i+k) else xs (i-(n-k))) ∧
        Frame before after base n)

/-- `upstream/bubble_sort.c`: return a nondecreasing permutation of the original signed ints.
Permutation preserves every multiplicity, including duplicates. Every byte outside the array
is unchanged. No initial sortedness, distinctness or small-length bound is assumed. -/
def bubble_sort : Prop :=
  ∀ (base : BitVec 64) (length : BitVec 32) (before : Memory) (xs : Values),
    let n := length.toNat
    WordsAt before base n xs → NoWrap base n →
    TerminatesWith v_bubble_sort.step (v_bubble_sort.initial base length before)
      (fun (_, after) ↦ ∃ ys,
        WordsAt after base n ys ∧ Increasing ys n ∧
        (contents ys n).Perm (contents xs n) ∧ Frame before after base n)

end ArrayExamples.Spec
