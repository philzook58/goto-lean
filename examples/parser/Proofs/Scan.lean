import GotoLean

/-! A pure, executable description of token boundaries in a terminated byte sequence. -/
namespace TokenParser
open GotoLean

def byte (bytes : List (BitVec 8)) (i : Nat) : BitVec 8 := bytes[i]?.getD 0

/-- The three boundaries found by skipping spaces, scanning a word, then skipping spaces. -/
structure Scan (bytes : List (BitVec 8)) where
  start : Nat
  stop : Nat
  next : Nat
  ordered : start ≤ stop ∧ stop ≤ next
  bounded : next < bytes.length
  leading : ∀ i, i < start → byte bytes i = 32
  first : byte bytes start ≠ 32
  word : ∀ i, start ≤ i → i < stop → byte bytes i ≠ 0 ∧ byte bytes i ≠ 32
  delimiter : byte bytes stop = 0 ∨ byte bytes stop = 32
  trailing : ∀ i, stop ≤ i → i < next → byte bytes i = 32
  last : byte bytes next ≠ 32


def findFrom (bytes : List (BitVec 8)) (origin : Nat) (p : BitVec 8 → Bool) : Nat :=
  origin + (bytes.drop origin).findIdx p

private theorem findFrom_spec (bytes : List (BitVec 8)) (p : BitVec 8 → Bool)
    (origin z : Nat) (hf : origin ≤ z) (hz : z < bytes.length) (hit : p (byte bytes z) = true) :
    origin ≤ findFrom bytes origin p ∧ findFrom bytes origin p ≤ z ∧
      p (byte bytes (findFrom bytes origin p)) = true ∧
      ∀ i, origin ≤ i → i < findFrom bytes origin p → p (byte bytes i) = false := by
  let ys := bytes.drop origin
  have index (j : Nat) (hj : j < ys.length) : ys[j] = byte bytes (origin + j) := by
    simp only [ys, byte, List.getElem_drop,
      List.getElem?_eq_getElem (l := bytes) (i := origin + j)
        (by simp only [ys, List.length_drop] at hj; omega), Option.getD_some]
  have iz : z - origin < ys.length := by simp only [ys, List.length_drop]; omega
  have pz : p ys[z - origin] = true := by rw [index _ iz]; simpa [Nat.add_sub_of_le hf] using hit
  have le : ys.findIdx p ≤ z - origin := by
    by_cases h : ys.findIdx p ≤ z - origin
    · exact h
    · have bad := List.not_of_lt_findIdx (xs := ys) (p := p) (by omega : z - origin < ys.findIdx p)
      rw [pz] at bad
      contradiction
  have bound : ys.findIdx p < ys.length := by omega
  have found := List.findIdx_getElem (xs := ys) (p := p) (w := bound)
  rw [index _ bound] at found
  refine ⟨by change origin ≤ origin + ys.findIdx p; omega,
    by change origin + ys.findIdx p ≤ z; omega, found, ?_⟩
  intro i hi he
  have hj : i - origin < ys.findIdx p := by change i < origin + ys.findIdx p at he; omega
  have bad := List.not_of_lt_findIdx (xs := ys) (p := p) hj
  rw [index _ (by have := List.findIdx_le_length (xs := ys) (p := p); omega)] at bad
  simpa [Nat.add_sub_of_le hi] using bad

private theorem scan_facts (bytes : List (BitVec 8)) (terminated : 0 ∈ bytes) :
    let start := findFrom bytes 0 (· != 32)
    let stop := findFrom bytes start (fun b ↦ b == 0 || b == 32)
    let next := findFrom bytes stop (· != 32)
    (start ≤ stop ∧ stop ≤ next) ∧ next < bytes.length ∧
      (∀ i, i < start → byte bytes i = 32) ∧ byte bytes start ≠ 32 ∧
      (∀ i, start ≤ i → i < stop → byte bytes i ≠ 0 ∧ byte bytes i ≠ 32) ∧
      (byte bytes stop = 0 ∨ byte bytes stop = 32) ∧
      (∀ i, stop ≤ i → i < next → byte bytes i = 32) ∧ byte bytes next ≠ 32 := by
  obtain ⟨z, hz, he⟩ := List.mem_iff_getElem.mp terminated
  have zero : byte bytes z = 0 := by simp [byte, List.getElem?_eq_getElem hz, he]
  obtain ⟨ha, haz, first, leading⟩ := findFrom_spec bytes (· != 32) 0 z
    (by omega) hz (by simp [zero])
  obtain ⟨hb, hbz, delimiter, word⟩ := findFrom_spec bytes (fun b ↦ b == 0 || b == 32)
    _ z haz hz (by simp [zero])
  obtain ⟨hc, hcz, last, trailing⟩ := findFrom_spec bytes (· != 32) _ z hbz hz (by simp [zero])
  refine ⟨⟨hb, hc⟩, by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi; have h := leading i (by omega) hi; simpa using h
  · simpa using first
  · intro i hi he; have h := word i hi he; simpa using h
  · simpa using delimiter
  · intro i hi he; have h := trailing i hi he; simpa using h
  · simpa using last

/-- Compute all three boundaries; termination by NUL supplies their bounds and character facts. -/
def scan (bytes : List (BitVec 8)) (terminated : 0 ∈ bytes) : Scan bytes := by
  obtain ⟨order, bound, leading, first, word, delimiter, trailing, last⟩ :=
    scan_facts bytes terminated
  exact ⟨_, _, _, order, bound, leading, first, word, delimiter, trailing, last⟩

end TokenParser
