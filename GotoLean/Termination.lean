import GotoLean.Basic

/-! Bounded completion from a natural-number ranking of the original generated blocks. -/
namespace GotoLean

/-- Every feasible path completes within this many blocks and satisfies `Q`.
As with `safe`, a false assumption discards its path. Failed checks remain failures. -/
def finishes (step : Step σ α) : Nat → σ → (α → Prop) → Prop
  | 0, _, _ => False
  | n + 1, s, Q => (step s).wp (Sum.elim (fun s' ↦ finishes step n s' Q) Q)

theorem finishes_mono (step : Step σ α) {a b : Nat} (h : a ≤ b) (s : σ) (Q : α → Prop) :
    finishes step a s Q → finishes step b s Q := by
  induction a generalizing b s with
  | zero => exact False.elim
  | succ a ih =>
    cases b with
    | zero => omega
    | succ b =>
      apply Action.wp_mono
      intro next hn
      cases next with
      | inl s' => exact ih (by omega) s' hn
      | inr r => exact hn

/-- Bounded completion includes the existing unbounded safety/partial-correctness contract. -/
theorem finishes_run (step : Step σ α) (fuel : Nat) (s : σ) (Q : α → Prop)
    (h : finishes step fuel s Q) : (run step s).wp Q := by
  induction fuel generalizing s with
  | zero => exact False.elim h
  | succ fuel ih =>
    intro n
    cases n with
    | zero => trivial
    | succ n =>
      apply Action.wp_mono _ _ h
      intro next hn
      cases next with
      | inl s' => exact ih s' hn n
      | inr r => exact hn

/-- Every feasible path reaches a state where `stop` holds within `n` blocks, without returning,
and that state satisfies `R`. `simp` evaluates `stop` on concrete block labels before it
unfolds further, so a proof can cover one segment of a function at a time. -/
def leadsTo (step : Step σ α) (stop : σ → Bool) : Nat → σ → (σ → Prop) → Prop
  | 0, _, _ => False
  | n + 1, s, R => (step s).wp
      (Sum.elim (fun s' ↦ if stop s' then R s' else leadsTo step stop n s' R) (fun _ ↦ False))

/-- Compose a segment with a proof for the states it stops at. -/
theorem finishes_of_leadsTo (step : Step σ α) (stop : σ → Bool) {R : σ → Prop} {Q : α → Prop}
    {m : Nat} (k : ∀ s, R s → finishes step m s Q) :
    ∀ n s, leadsTo step stop n s R → finishes step (n + m) s Q
  | 0, _, h => False.elim h
  | n + 1, s, h => by
    rw [show n + 1 + m = (n + m) + 1 by omega]
    apply Action.wp_mono _ _ h
    intro next hn
    cases next with
    | inr _ => exact False.elim hn
    | inl s' =>
      simp only [Sum.elim] at hn
      split at hn
      · exact finishes_mono step (by omega) s' Q (k s' hn)
      · exact finishes_of_leadsTo step stop k n s' hn

/-- The rank includes ordinary control-flow blocks, not just source-level loop iterations. -/
theorem finishes_of_rank (step : Step σ α) (I : σ → Prop) (rank : σ → Nat) (Q : α → Prop)
    (decreases : ∀ s, I s → (step s).wp
      (Sum.elim (fun s' ↦ I s' ∧ rank s' < rank s) Q))
    (s : σ) (hi : I s) : finishes step (rank s + 1) s Q := by
  induction h : rank s using Nat.strongRecOn generalizing s with
  | ind n ih =>
    unfold finishes
    apply Action.wp_mono _ _ (decreases s hi)
    intro next hn
    cases next with
    | inr r => exact hn
    | inl s' =>
      obtain ⟨hi', lt⟩ := hn
      exact finishes_mono step (by omega) s' Q (ih (rank s') (by omega) s' hi' rfl)

end GotoLean
