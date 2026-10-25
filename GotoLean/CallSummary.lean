import GotoLean.Calls
import GotoLean.Termination

/-! A proved callee contract can resume an arbitrary caller in the same program body. -/
namespace GotoLean

/-- Lift a typed postcondition through a return constructor, excluding other variants.
The payload may include both the result and memory, so callers can state frame conditions. -/
def ReturnPost (tag : ρ → α) (post : ρ → Prop) (value : α) : Prop :=
  ∃ result, value = tag result ∧ post result

/-- Attach a caller continuation to a completed function, preserving internal calls and checks. -/
theorem finishes_resume (body : σ → Action (Transfer σ α))
    (calleeFinish : α → Action β) (callerFinish : α → Action γ)
    (resume : α → Action σ) (outer : List (α → Action σ)) (tail : Nat)
    (P : β → Prop) (Q : γ → Prop)
    (returns : ∀ value, (calleeFinish value).wp P →
      (resume value).wp (fun next ↦ finishes (callStep body callerFinish) tail (next, outer) Q))
    (fuel : Nat) (frame : σ) (inner : List (α → Action σ))
    (h : finishes (callStep body calleeFinish) fuel (frame, inner) P) :
    finishes (callStep body callerFinish) (fuel+tail) (frame, inner ++ resume :: outer) Q := by
  induction fuel generalizing frame inner with
  | zero => exact False.elim h
  | succ fuel ih =>
    rw [show fuel+1+tail = (fuel+tail)+1 by omega]
    change (Action.bind (body frame) _).wp _ at h ⊢
    rw [Action.wp_bind] at h ⊢
    apply Action.wp_mono _ _ h
    intro transfer ht
    cases transfer with
    | next next => exact ih next inner ht
    | call callee k => exact ih callee (k :: inner) ht
    | returned value =>
      cases inner with
      | nil =>
        change (Action.bind (calleeFinish value) _).wp _ at ht
        rw [Action.wp_bind] at ht
        change (calleeFinish value).wp P at ht
        change (Action.bind (resume value) _).wp _
        rw [Action.wp_bind]
        apply Action.wp_mono _ _ (returns value ht)
        intro next hn
        exact finishes_mono _ (by omega) _ _ hn
      | cons k rest =>
        change (Action.bind (k value) _).wp _ at ht ⊢
        rw [Action.wp_bind] at ht ⊢
        apply Action.wp_mono _ _ ht
        intro next hn
        exact ih next rest hn

end GotoLean
