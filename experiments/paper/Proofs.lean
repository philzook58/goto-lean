import GotoLean.Audit
import PaperAbs
import PaperBinsearch
import PaperBefore
import PaperArrayAssume

open GotoLean

theorem abs_overflow : (v_abs.eval 2147483648 10 [0]).1.isAssertionFailure = true := by
  decide +kernel

#guard (v_binsearch.eval 0 100 [0, 0, 0, 0]).1 == .returned 8
#guard (v_one_to_hundred.eval 20 [0, 0, 100]).1.isAssertionFailure

/-- a[0] is zero and a[1] is negative: restricting the first read does not restrict the second. -/
theorem array_counterexample : ¬ v_main.run.wp (fun _ => True) :=
  (failure_refutes v_main.step (fun f => reprStr f.1) v_main.initial 20
    [18446744069414584320, 0, 0, 0, 1] (by decide +kernel) (fun _ => True)).2

#check_axioms abs_overflow
#check_axioms array_counterexample
