import GotoLean.Calls

/-! Modular safety and partial-correctness contracts for the existing call-stack interpreter. -/
namespace GotoLean

variable {σ α β : Type}

/-- A call proves its callee's contract and uses that contract when resuming the caller. -/
def Transfer.wp (transfer : Transfer σ α) (I : σ → (α → Prop) → Prop) (Q : α → Prop) : Prop :=
  match transfer with
  | .next frame => I frame Q
  | .returned value => Q value
  | .call callee resume => ∃ R, I callee R ∧ ∀ value, R value → (resume value).wp (I · Q)

private def stackContract (I : σ → (α → Prop) → Prop) (finish : α → Action β) (Q : β → Prop) :
    List (α → Action σ) → (α → Prop) → Prop
  | [], R => ∀ value, R value → (finish value).wp Q
  | resume :: rest, R => ∃ S, stackContract I finish Q rest S ∧
      ∀ value, R value → (resume value).wp (I · S)

open Std.WP Lean.Order

/-- Local contracts imply safety for every finite execution, including recursive calls.
The preservation premise checks all callees; contracts are proved, never assumed as axioms. -/
@[spec] theorem calls_spec (body : σ → Action (Transfer σ α)) (finish : α → Action β)
    (I : σ → (α → Prop) → Prop) (initial : σ) (R : α → Prop) (Q : β → Prop)
    (preserves : ∀ frame post, I frame post → (body frame).wp (Transfer.wp · I post))
    (returns : ∀ value, R value → (finish value).wp Q) :
    ⦃I initial R⦄ run (callStep body finish) (initial, []) ⦃Q⦄ := by
  let J : CallState σ α → Prop := fun (frame, stack) ↦
    ∃ post, I frame post ∧ stackContract I finish Q stack post
  have step : ∀ state, J state →
      (callStep body finish state).wp (Sum.elim J Q) := by
    rintro ⟨frame, stack⟩ ⟨post, hf, hk⟩
    unfold callStep
    change (Action.bind (body frame) _).wp _
    rw [Action.wp_bind]
    apply Action.wp_mono _ _ (preserves frame post hf)
    intro transfer ht
    cases transfer with
    | next next => exact ⟨post, ht, hk⟩
    | call callee resume =>
      obtain ⟨calleePost, hc, hr⟩ := ht
      exact ⟨calleePost, hc, post, hk, hr⟩
    | returned value =>
      cases stack with
      | nil =>
        change (Action.bind (finish value)
          (fun result ↦ .done (Sum.inr result : Next (CallState σ α) β))).wp _
        rw [Action.wp_bind]
        exact hk value ht
      | cons resume rest =>
        obtain ⟨callerPost, hrest, hr⟩ := hk
        change (Action.bind (resume value)
          (fun next ↦ .done (Sum.inl (next, rest) : Next (CallState σ α) β))).wp _
        rw [Action.wp_bind]
        apply Action.wp_mono _ _ (hr value ht)
        intro next hn
        exact ⟨callerPost, hn, hrest⟩
  constructor
  intro hi
  exact (run_spec _ _ J Q step).le_wp ⟨R, hi, returns⟩

end GotoLean
