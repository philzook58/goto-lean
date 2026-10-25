import GotoLean.Audit
import LeakGood

open GotoLean

/-- The whole startup/program execution passes CBMC's inserted leak assertion.
Choice 13 records the allocation; the same choice exposes the leak in LeakUnsafe.lean. -/
theorem leak_checked_return : ∃ m,
    Executes v___CPROVER__start.step v___CPROVER__start.initial (.returned ((), m)) := by
  let out := (v___CPROVER__start.eval 100 ((List.replicate 100 0).set 13 1)).1
  have returned : (match out with | .returned _ => true | _ => false) = true := by decide +kernel
  have execution := evalLoop_exec v___CPROVER__start.step (fun f ↦ reprStr f.1)
    100 v___CPROVER__start.initial ((List.replicate 100 0).set 13 1)
  change out.Corresponds (Executes v___CPROVER__start.step v___CPROVER__start.initial) at execution
  cases h : out <;> simp [h] at returned
  rename_i value
  rcases value with ⟨result, m⟩
  cases result
  exact ⟨m, by simpa [h, Outcome.Corresponds] using execution⟩

#check_axioms leak_checked_return
