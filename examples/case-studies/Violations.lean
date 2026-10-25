import Generated.JsonClaim
import Generated.BigSlide
import Generated.DeletedClaim
import Generated.DoubleMerge
import Generated.Sites
import GotoLean.Audit

open GotoLean
set_option autoImplicit false
set_option maxRecDepth 4096

/-- Tokenizing truX does not establish that it is valid JSON. -/
theorem tokenizer_is_not_validator :
    ¬ v_json_validation_claim.run.wp (fun _ ↦ True) := by
  have h : (v_json_validation_claim.eval 1000 (List.replicate 1024 0)).fst =
      .assertionFailed ViolationSites.jsonClaim := by decide +kernel
  exact (failure_refutes v_json_validation_claim.step (fun f ↦ reprStr f.1)
    v_json_validation_claim.initial 1000 (List.replicate 1024 0)
    (by simp only [v_json_validation_claim.eval] at h; simp only [h, Outcome.isAssertionFailure])
    (fun _ ↦ True)).2

/-- The original row routine has an invalid 32-bit score shift for exponent 31 pairs. -/
theorem large_tile_shift : ¬ v_slide_large.run.wp (fun _ ↦ True) := by
  have h : (v_slide_large.eval 1000 (List.replicate 1024 0)).fst =
      .assertionFailed ViolationSites.bigSlide := by decide +kernel
  exact (failure_refutes v_slide_large.step (fun f ↦ reprStr f.1)
    v_slide_large.initial 1000 (List.replicate 1024 0)
    (by simp only [v_slide_large.eval] at h; simp only [h, Outcome.isAssertionFailure])
    (fun _ ↦ True)).2

/-- Deleting a key must make it absent, even when its old bucket remains a tombstone. -/
theorem deleted_key_is_absent : ¬ v_lookup_deleted_claim.run.wp (fun _ ↦ True) := by
  have h : (v_lookup_deleted_claim.eval 1000 (List.replicate 1024 0)).fst =
      .assertionFailed ViolationSites.deletedClaim := by decide +kernel
  exact (failure_refutes v_lookup_deleted_claim.step (fun f ↦ reprStr f.1)
    v_lookup_deleted_claim.initial 1000 (List.replicate 1024 0)
    (by simp only [v_lookup_deleted_claim.eval] at h; simp only [h, Outcome.isAssertionFailure])
    (fun _ ↦ True)).2

/-- Removing the merge barrier violates the caller's once-per-move merge property. -/
theorem double_merge_mutation : ¬ v_slide_no_double_merge.run.wp (fun _ ↦ True) := by
  have h : (v_slide_no_double_merge.eval 1000 (List.replicate 1024 0)).fst =
      .assertionFailed ViolationSites.doubleMerge := by decide +kernel
  exact (failure_refutes v_slide_no_double_merge.step (fun f ↦ reprStr f.1)
    v_slide_no_double_merge.initial 1000 (List.replicate 1024 0)
    (by simp only [v_slide_no_double_merge.eval] at h; simp only [h, Outcome.isAssertionFailure])
    (fun _ ↦ True)).2

#check_axioms tokenizer_is_not_validator
#check_axioms large_tile_shift
#check_axioms deleted_key_is_absent
#check_axioms double_merge_mutation
