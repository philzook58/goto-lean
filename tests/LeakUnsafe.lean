import GotoLean.Audit
import LeakBad

open GotoLean

private def choices := (List.replicate 100 0).set 13 1
private def leakSite := "__CPROVER__start: GOTO 3; property __CPROVER__start.memory-leak.1; " ++
  "dynamically allocated memory never freed in __CPROVER_memory_leak == NULL"

/-- Losing the allocation reaches the actual imported memory-leak property and refutes safety. -/
theorem leak_counterexample :
    Executes v___CPROVER__start.step v___CPROVER__start.initial (.assertionFailed leakSite) ∧
    ¬ v___CPROVER__start.run.wp (fun _ ↦ True) := by
  have result : (v___CPROVER__start.eval 100 choices).1 = .assertionFailed leakSite := by
    decide +kernel
  have execution := evalLoop_exec v___CPROVER__start.step (fun f ↦ reprStr f.1)
    100 v___CPROVER__start.initial choices
  have failure := failure_refutes v___CPROVER__start.step (fun f ↦ reprStr f.1)
    v___CPROVER__start.initial 100 choices
    (by simp only [show (evalLoop _ _ _ _ _).1 = _ from result, Outcome.isAssertionFailure])
    (fun _ ↦ True)
  exact ⟨
    by simpa [show (evalLoop _ _ _ _ _).1 = _ from result, Outcome.Corresponds] using execution,
    failure.2⟩

#check_axioms leak_counterexample
