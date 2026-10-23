import GotoLean.Basic

namespace GotoLean

/-- Distinct outcomes keep bounds and discarded assumptions separate from successful returns. -/
inductive Outcome (α : Type) where
  | returned (value : α)
  | assertionFailed (site : Site)
  | assumptionRejected (site : Site)
  | choiceError (site : Site)
  | exhausted (block : String)
  deriving Repr, BEq, DecidableEq

/-- A computable predicate for compact, kernel-checked counterexample certificates. -/
def Outcome.isAssertionFailure : Outcome α → Bool
  | .assertionFailed _ => true
  | _ => false

/-- A safety claim places no obligation on discarded paths or runner resource/input errors. -/
def Outcome.Satisfies (Q : α → Prop) : Outcome α → Prop
  | .returned a => Q a
  | .assertionFailed _ => False
  | _ => True

/-- Concrete choices are unsigned integers, checked against the requested bit width. -/
def Action.eval (x : Action α) (choices : List Nat) : Outcome α × List Nat :=
  match x with
  | .done a => (.returned a, choices)
  | .choose site w k => match choices with
      | [] => (.choiceError site, [])
      | v :: rest => if v < 2 ^ w then (k (BitVec.ofNat w v)).eval rest
          else (.choiceError site, choices)
  | .check site b k => if b then k.eval choices else (.assertionFailed site, choices)
  | .assume site b k => if b then k.eval choices else (.assumptionRejected site, choices)

/-- The concrete interpreter respects the universal finite-block specification. -/
theorem Action.eval_sound (x : Action α) (choices : List Nat) (Q : α → Prop)
    (h : x.wp Q) : (x.eval choices).1.Satisfies Q := by
  induction x generalizing choices with
  | done a => exact h
  | choose site w k ih =>
    cases choices with
    | nil => trivial
    | cons v rest =>
      simp only [Action.eval]
      split
      · exact ih _ rest (h _)
      · trivial
  | check site b k ih =>
    cases b with
    | false => exact Bool.noConfusion h.1
    | true => exact ih choices h.2
  | assume site b k ih =>
    cases b with
    | false => trivial
    | true => exact ih choices (h rfl)

/-- Finite operational behavior; input errors and fuel exhaustion are runner outcomes only. -/
inductive Action.Exec : Action α → Outcome α → Prop where
  | done (a : α) : Exec (.done a) (.returned a)
  | choose {site w k out} (v : BitVec w) : Exec (k v) out → Exec (.choose site w k) out
  | check {site k out} : Exec k out → Exec (.check site true k) out
  | failed (site : Site) (k : Action α) : Exec (.check site false k) (.assertionFailed site)
  | assume {site k out} : Exec k out → Exec (.assume site true k) out
  | rejected (site : Site) (k : Action α) : Exec (.assume site false k) (.assumptionRejected site)

/-- Resource/input errors make no claim of an observed program behavior. -/
def Outcome.Corresponds (R : Outcome α → Prop) : Outcome α → Prop
  | .choiceError _ | .exhausted _ => True
  | out => R out

theorem Outcome.Corresponds.map {R S : Outcome α → Prop} {out : Outcome α}
    (h : ∀ o, R o → S o) (hr : out.Corresponds R) : out.Corresponds S := by
  cases out <;> first | trivial | exact h _ hr

/-- Every concrete return, failed check or rejected assumption has an operational witness. -/
theorem Action.eval_exec (x : Action α) (choices : List Nat) :
    (x.eval choices).1.Corresponds (Action.Exec x) := by
  induction x generalizing choices with
  | done a => exact .done a
  | choose site w k ih =>
    cases choices with
    | nil => trivial
    | cons v rest =>
      simp only [Action.eval]
      split
      · exact (ih _ rest).map (fun _ h => .choose _ h)
      · trivial
  | check site b k ih =>
    cases b with
    | false => exact .failed site k
    | true => exact (ih choices).map (fun _ h => .check h)
  | assume site b k ih =>
    cases b with
    | false => exact .rejected site k
    | true => exact (ih choices).map (fun _ h => .assume h)

/-- Explicit blocks are the only unit charged against the execution bound. -/
def evalLoop (step : Step σ α) (describe : σ → String) :
    Nat → σ → List Nat → Outcome α × List Nat
  | 0, s, choices => (.exhausted (describe s), choices)
  | n + 1, s, choices =>
    match (step s).eval choices with
    | (.returned (.inl s'), rest) => evalLoop step describe n s' rest
    | (.returned (.inr a), rest) => (.returned a, rest)
    | (.assertionFailed site, rest) => (.assertionFailed site, rest)
    | (.assumptionRejected site, rest) => (.assumptionRejected site, rest)
    | (.choiceError site, rest) => (.choiceError site, rest)
    | (.exhausted block, rest) => (.exhausted block, rest)

/-- A finite sequence of generated blocks ending in an observable program outcome. -/
inductive Executes (step : Step σ α) : σ → Outcome α → Prop where
  | returned {s a} : (step s).Exec (.returned (.inr a)) → Executes step s (.returned a)
  | next {s s' out} : (step s).Exec (.returned (.inl s')) →
      Executes step s' out → Executes step s out
  | failed {s site} : (step s).Exec (.assertionFailed site) →
      Executes step s (.assertionFailed site)
  | rejected {s site} : (step s).Exec (.assumptionRejected site) →
      Executes step s (.assumptionRejected site)

/-- Concrete execution replays a possible finite execution of the same block definitions. -/
theorem evalLoop_exec (step : Step σ α) (describe : σ → String) (fuel : Nat)
    (s : σ) (choices : List Nat) :
    (evalLoop step describe fuel s choices).1.Corresponds (Executes step s) := by
  induction fuel generalizing s choices with
  | zero => trivial
  | succ n ih =>
    have hs := Action.eval_exec (step s) choices
    unfold evalLoop
    generalize he : (step s).eval choices = result at *
    rcases result with ⟨out, rest⟩
    cases out with
    | returned next =>
      cases next with
      | inl s' => exact (ih s' rest).map (fun _ h => .next hs h)
      | inr a => exact .returned hs
    | assertionFailed site => exact .failed hs
    | assumptionRejected site => exact .rejected hs
    | choiceError site => trivial
    | exhausted block => trivial

/-- Finite-block safety implies sound concrete results and excludes concrete assertion failures. -/
theorem evalLoop_sound (step : Step σ α) (describe : σ → String) (fuel : Nat)
    (s : σ) (choices : List Nat) (Q : α → Prop) (h : safe step fuel s Q) :
    (evalLoop step describe fuel s choices).1.Satisfies Q := by
  induction fuel generalizing s choices with
  | zero => trivial
  | succ n ih =>
    have hs := Action.eval_sound (step s) choices _ h
    unfold evalLoop
    generalize he : (step s).eval choices = result at *
    rcases result with ⟨out, rest⟩
    cases out with
    | returned next =>
      cases next with
      | inl s' => exact ih s' rest hs
      | inr a => exact hs
    | assertionFailed site => exact hs
    | assumptionRejected site => trivial
    | choiceError site => trivial
    | exhausted block => trivial

/-- Unbounded proofs apply to every concrete bound and every valid choice stream. -/
theorem run_eval_sound (step : Step σ α) (describe : σ → String) (s : σ)
    (Q : α → Prop) (h : (run step s).wp Q) (fuel : Nat) (choices : List Nat) :
    (evalLoop step describe fuel s choices).1.Satisfies Q :=
  evalLoop_sound step describe fuel s choices Q (h fuel)

/-- A replayed failed assertion witnesses reachability and refutes every safety postcondition. -/
theorem failure_refutes (step : Step σ α) (describe : σ → String) (initial : σ)
    (fuel : Nat) (choices : List Nat)
    (failed : (evalLoop step describe fuel initial choices).1.isAssertionFailure = true)
    (Q : α → Prop) :
    (∃ site, Executes step initial (.assertionFailed site)) ∧ ¬(run step initial).wp Q := by
  have executed := evalLoop_exec step describe fuel initial choices
  have sound := fun h => run_eval_sound step describe initial Q h fuel choices
  generalize hout : (evalLoop step describe fuel initial choices).1 = out at *
  cases out <;> simp_all [Outcome.isAssertionFailure, Outcome.Corresponds, Outcome.Satisfies]
  exact ⟨_, executed⟩

end GotoLean
