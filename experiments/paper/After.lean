import GotoLean.Audit
import PaperAfter

open GotoLean

-- The paper's prose says this passes; 100 is still allowed by its assumption.
theorem after_counterexample : ¬ v_one_to_hundred.run.wp (fun _ => True) :=
  (failure_refutes v_one_to_hundred.step (fun f => reprStr f.1) v_one_to_hundred.initial
    20 [0, 0, 100] (by decide +kernel) (fun _ => True)).2

#check_axioms after_counterexample
