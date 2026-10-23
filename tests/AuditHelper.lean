/-! Deliberately untrusted fixtures: used only to verify that the audit rejects them. -/
namespace AuditFixtures

axiom untrusted : True

theorem inherited : True := untrusted

/-- warning: declaration uses `sorry` -/
#guard_msgs in
theorem unfinished : True := by sorry

end AuditFixtures
