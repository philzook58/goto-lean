import GotoLean.Termination

/-! Checked finite paths between user-selected checkpoints in the original block interpreter. -/
namespace GotoLean

/-- Execute at least one block, stopping at a return or the next checkpoint.
Running out of path budget is a failed check, never a silently discarded path. -/
def path (step : Step σ α) (cut : σ → Bool) : Nat → Step σ α
  | 0, s => .check "proof path budget exhausted" false (.done (.inl s))
  | n + 1, s => do
    match ← step s with
    | .inr value => pure (.inr value)
    | .inl next => if cut next then pure (.inl next) else path step cut n next

/-- Completing a path and its continuation completes the original blocks. -/
theorem path_finishes (step : Step σ α) (cut : σ → Bool) (budget tail : Nat)
    (s : σ) (Q : α → Prop)
    (h : (path step cut budget s).wp
      (Sum.elim (fun next ↦ finishes step tail next Q) Q)) :
    finishes step (budget + tail) s Q := by
  induction budget generalizing s with
  | zero => exact Bool.noConfusion h.1
  | succ budget ih =>
    change (Action.bind (step s) _).wp _ at h
    rw [Action.wp_bind] at h
    rw [show budget + 1 + tail = (budget + tail) + 1 by omega]
    change (step s).wp _
    apply Action.wp_mono _ _ h
    intro next hn
    cases next with
    | inr value => exact hn
    | inl next =>
      dsimp only at hn
      split at hn
      · exact finishes_mono step (by omega) next Q hn
      · exact ih next hn

/-- A bounded proof over paths is a bounded proof over the original program.
No CFG reconstruction, acyclicity assumption, or additional trusted transformation is needed. -/
theorem finishes_paths (step : Step σ α) (cut : σ → Bool) (budget count : Nat)
    (s : σ) (Q : α → Prop) (h : finishes (path step cut budget) count s Q) :
    finishes step (budget * count) s Q := by
  induction count generalizing s with
  | zero => exact False.elim h
  | succ count ih =>
    rw [Nat.mul_succ, Nat.add_comm]
    apply path_finishes step cut budget (budget * count) s Q
    apply Action.wp_mono _ _ h
    intro next hn
    cases next with
    | inr value => exact hn
    | inl next => exact ih next hn

end GotoLean
