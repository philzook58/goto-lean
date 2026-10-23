import GotoLean.Basic

namespace GotoLean

/-- A generated block continues, enters a callee, or returns to its caller. -/
inductive Transfer (σ α : Type) where
  | next (frame : σ)
  | call (callee : σ) (resume : α → Action σ)
  | returned (value : α)

/-- Caller continuations capture locals; the callee returns the current shared memory. -/
abbrev CallState (σ α : Type) := σ × List (α → Action σ)

/-- One ordinary block step, including call-stack push/pop. Fuel still counts blocks. -/
def callStep (body : σ → Action (Transfer σ α)) (finish : α → Action β) :
    Step (CallState σ α) β := fun (frame, stack) => do
  match ← body frame with
  | .next frame => pure (.inl (frame, stack))
  | .call callee resume => pure (.inl (callee, resume :: stack))
  | .returned value =>
    match stack with
    | [] => return .inr (← finish value)
    | resume :: rest => return .inl (← resume value, rest)

end GotoLean
