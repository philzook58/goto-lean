import GotoLean.Audit
import Uninitialized
import Abs32
import Abs64
import BeforeAssume
import AfterAssume
import LockBug

open GotoLean

-- These are kernel reductions of generated programs, rather than native_decide evaluations.
theorem uninitialized_failure :
    (v_uninitialized.eval 10 [12345]).1.isAssertionFailure = true := by decide
theorem abs32_failure :
    (v_abs32.eval 0x80000000 10 [0]).1.isAssertionFailure = true := by decide
theorem abs64_failure :
    (v_abs64.eval 0x8000000000000000 10 [0]).1.isAssertionFailure = true := by decide
theorem before_failure :
    (v_before_assume.eval 0x80000000 10 []).1.isAssertionFailure = true := by decide
theorem after_failure :
    (v_after_assume.eval 100 10 []).1.isAssertionFailure = true := by decide
-- Entry declarations, then a temporary declaration and acquisition bit per iteration.
theorem lock_failure :
    (v_lock_bug.eval 98304 100 [0, 0, 0, 1, 0, 0, 0, 0]).1.isAssertionFailure = true := by decide
-- The CBMC trace above has a shorter witness: two unsuccessful acquisitions suffice.
theorem lock_short_failure :
    (v_lock_bug.eval 2 100 [0, 0, 0, 0, 0, 0]).1.isAssertionFailure = true := by decide

-- An explicit finite operational witness and refutation of every claimed safety postcondition.
theorem uninitialized_counterexample (Q : BitVec 32 → Prop) :
    (∃ site, Executes v_uninitialized.step v_uninitialized.initial (.assertionFailed site)) ∧
      ¬v_uninitialized.run.wp Q :=
  failure_refutes v_uninitialized.step (fun f => reprStr f.1) (v_uninitialized.initial)
    10 [12345] uninitialized_failure Q

theorem abs32_counterexample (Q : BitVec 32 → Prop) :
    (∃ site, Executes v_abs32.step (v_abs32.initial 0x80000000) (.assertionFailed site)) ∧
      ¬(v_abs32.run 0x80000000).wp Q :=
  failure_refutes v_abs32.step (fun f => reprStr f.1) (v_abs32.initial 0x80000000)
    10 [0] abs32_failure Q

theorem abs64_counterexample (Q : BitVec 64 → Prop) :
    (∃ site, Executes v_abs64.step (v_abs64.initial 0x8000000000000000) (.assertionFailed site)) ∧
      ¬(v_abs64.run 0x8000000000000000).wp Q :=
  failure_refutes v_abs64.step (fun f => reprStr f.1) (v_abs64.initial 0x8000000000000000)
    10 [0] abs64_failure Q

theorem before_counterexample (Q : BitVec 32 → Prop) :
    (∃ site, Executes v_before_assume.step (v_before_assume.initial 0x80000000)
      (.assertionFailed site)) ∧ ¬(v_before_assume.run 0x80000000).wp Q :=
  failure_refutes v_before_assume.step (fun f => reprStr f.1) (v_before_assume.initial 0x80000000)
    10 [] before_failure Q

theorem after_counterexample (Q : BitVec 32 → Prop) :
    (∃ site, Executes v_after_assume.step (v_after_assume.initial 100) (.assertionFailed site)) ∧
      ¬(v_after_assume.run 100).wp Q :=
  failure_refutes v_after_assume.step (fun f => reprStr f.1) (v_after_assume.initial 100)
    10 [] after_failure Q

theorem lock_counterexample (Q : BitVec 32 → Prop) :
    (∃ site, Executes v_lock_bug.step (v_lock_bug.initial 98304) (.assertionFailed site)) ∧
      ¬(v_lock_bug.run 98304).wp Q :=
  failure_refutes v_lock_bug.step (fun f => reprStr f.1) (v_lock_bug.initial 98304)
    100 [0, 0, 0, 1, 0, 0, 0, 0] lock_failure Q

#check_axioms uninitialized_counterexample
#check_axioms abs32_counterexample
#check_axioms abs64_counterexample
#check_axioms before_counterexample
#check_axioms after_counterexample
#check_axioms lock_counterexample
