import GotoLean
import GotoLean.Audit
import AuditHelper

-- Standard axioms and axiom-free proofs remain accepted.
#check_axioms GotoLean.run_spec, GotoLean.run_eval_sound

namespace AuditTests

theorem clean : True := trivial
#check_axioms clean

-- These are imported dependencies, not occurrences found by scanning this file.
/-- error: axiom audit failed for AuditFixtures.inherited: [AuditFixtures.untrusted] -/
#guard_msgs in
#check_axioms AuditFixtures.inherited

/-- error: axiom audit failed for AuditFixtures.unfinished: [sorryAx] -/
#guard_msgs in
#check_axioms AuditFixtures.unfinished

-- A typo must not silently audit an empty list of claims.
/-- error: Unknown constant `AuditFixtures.missing` -/
#guard_msgs in
#check_axioms AuditFixtures.missing

end AuditTests
