import GotoLean.Audit
import BufferOverflow
import Binsearch

open GotoLean

-- The bounds assertion was inserted by CBMC, not invented by the Lean printer.
theorem buffer_failure :
    (v_buffer_overflow.eval 10 [0]).1.isAssertionFailure = true := by decide

theorem buffer_counterexample (Q : BitVec 32 → Prop) :
    (∃ site, Executes v_buffer_overflow.step v_buffer_overflow.initial (.assertionFailed site)) ∧
      ¬v_buffer_overflow.run.wp Q :=
  failure_refutes v_buffer_overflow.step (fun f => reprStr f.1) v_buffer_overflow.initial
    10 [0] buffer_failure Q

-- Concrete searches with a zero-filled array; these are not universal search-correctness proofs.
#guard (v_binsearch.eval 0 100 [0, 0, 0, 0]).1 == .returned 8
#guard (v_binsearch.eval 1 100 (List.replicate 8 0)).1 == .returned 4294967295

#check_axioms buffer_counterexample
