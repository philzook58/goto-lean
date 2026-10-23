import Spec
import Proofs

/-! These are checked links from the reviewable claims to the existing implementation proofs.
This file contains no new algorithm argument or assumed contract. -/
namespace ArrayExamples.Verified

/-- The generated lower-bound program satisfies `Spec.lower_bound`. -/
theorem lower_bound : Spec.lower_bound := by
  intro base length key before xs
  dsimp only
  intro mem sorted
  refine ⟨8*(length.toNat+1)+6, ?_⟩
  simpa only [Partition, Nat.le_refl, true_and, and_assoc] using
    LowerBound.terminates base length key before xs mem sorted

/-- The generated reversal program satisfies `Spec.reverse`. -/
theorem reverse : Spec.reverse := by
  intro base length before xs
  dsimp only
  intro mem nowrap
  exact ⟨_, Reverse.verify base length before xs mem nowrap⟩

/-- The generated fill program satisfies `Spec.fill`. -/
theorem fill : Spec.fill := by
  intro base length value before xs
  dsimp only
  intro mem nowrap
  exact ⟨_, Fill.verify base length value before xs mem nowrap⟩

/-- The generated first-match search satisfies `Spec.find`. -/
theorem find : Spec.find := by
  intro base length key before xs
  dsimp only
  intro mem
  refine ⟨4*(length.toNat+2), ?_⟩
  simpa only [Find.Found, and_assoc] using Find.verify base length key before xs mem

/-- The generated prefix scan satisfies `Spec.is_sorted_until`. -/
theorem is_sorted_until : Spec.is_sorted_until := by
  intro base length before xs
  dsimp only
  intro mem
  refine ⟨4*(length.toNat+2), ?_⟩
  simpa only [IsSortedUntil.Prefix, and_assoc] using IsSortedUntil.verify base length before xs mem

/-- The generated three-call rotation satisfies `Spec.rotate`. -/
theorem rotate : Spec.rotate := by
  intro base pivot length before xs
  dsimp only
  intro bound mem nowrap
  exact ⟨_, Rotate.verify base pivot length before xs bound mem nowrap⟩

/-- The generated nested-loop sort satisfies `Spec.bubble_sort`. -/
theorem bubble_sort : Spec.bubble_sort := by
  intro base length before xs
  dsimp only
  intro mem nowrap
  exact ⟨_, BubbleSort.verify base length before xs mem nowrap⟩

end ArrayExamples.Verified
