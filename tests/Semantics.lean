import GotoLean.Audit
import GotoLean

open GotoLean Std.WP Lean.Order
set_option experimental.vcgen true

-- Default memory retains the reserved null/invalid slots and all field defaults.
example : (default : Memory) = {} := rfl

example : ⦃True⦄ (do
    let x ← choose "choice" 8
    assume "bound" (x.toNat < 10)
    check "assertion" (x.toNat ≤ 9)
    pure x : Action (BitVec 8)) ⦃fun x => x.toNat < 10⦄ := by
  vcgen
  all_goals simp_all [Action.wp_apply_eq, Action.wp_pure]
  all_goals omega

example : ¬ (check "bad" false).wp (fun _ => True) := by
  simp [check, Action.wp]

example : (do
    assume "pruned" false
    check "unreachable" false : Action Unit).wp (fun _ => False) := by
  simp [assume, check, Bind.bind, Action.bind, Action.wp]

example : (choose "choice" 8).eval [256] = (.choiceError "choice", [256]) := by decide
example : (choose "choice" 8).eval [] = (.choiceError "choice", []) := by decide
example : (choose "choice" 8).eval [42, 9] = (.returned 42, [9]) := by decide
example : (check "bad" false).eval [] = (.assertionFailed "bad", []) := by decide
example : (assume "pruned" false).eval [] = (.assumptionRejected "pruned", []) := by decide
example : (Outcome.returned (43 : BitVec 32)).getValue? = some 43 := rfl
example : ([.assertionFailed "check", .assumptionRejected "assume",
    .choiceError "choice", .exhausted "block"] : List (Outcome (BitVec 32))).all
    (fun out ↦ out.getValue? != some 0) = true := by decide
example : (divide "zero" false false (7 : BitVec 8) 0).eval [99] =
    (.returned 99, []) := by decide

private def spin : Step Unit Unit := fun _ => pure (.inl ())
example : (run spin ()).wp (fun _ => False) := by
  apply (run_spec spin () (fun _ => True) (fun _ => False) ?_).le_wp trivial
  intro s _; trivial

private def badSpin : Step Unit Unit := fun _ => do
  check "before divergence" false
  pure (.inl ())
example : ¬ (run badSpin ()).wp (fun _ => True) := by
  intro h
  have hn := h 1
  exact Bool.noConfusion hn.1

example : (evalLoop spin (fun _ => "spin") 3 () []).1 = .exhausted "spin" := by decide
example : (evalLoop badSpin (fun _ => "spin") 3 () []).1 =
    .assertionFailed "before divergence" := by decide

#check_axioms GotoLean.run_spec
#check_axioms GotoLean.run_eval_sound

-- Value globals survive ordinary object allocation, stores and lifetime updates.
example (m : Memory) (p : BitVec 64) (b : Array (BitVec 8)) :
    ((m.setGlobal "state" (37 : BitVec 32)).put 2 b).getGlobal "state" (0 : BitVec 32) =
      37 := by simp [Memory.getGlobal, Memory.setGlobal, Memory.put]

example : (Memory.objectSize "size" 56 64
    { objects := #[none, none, some #[0, 1, 2]] }
    (Pointer.make 56 2 100 : BitVec 64)).eval [] = (.returned 3, []) := by decide

example : (Memory.objectSize "size" 56 64 {}
    (Pointer.make 56 2 0 : BitVec 64)).eval [73] = (.returned 73, []) := by decide
