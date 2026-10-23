import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Build-time axiom checks for explicitly named claims; no runtime dependency. -/
open Lean Elab Command

/-- Reject transitive dependencies outside the project's standard-axiom policy. -/
elab "#check_axioms " claims:ident,+ : command => do
  for claim in claims.getElems do
    let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo claim
    let axioms ← collectAxioms name
    let unexpected := axioms.filter fun dependency ↦
      ![``propext, ``Quot.sound, ``Classical.choice].contains dependency
    unless unexpected.isEmpty do
      throwErrorAt claim "axiom audit failed for {name}: {unexpected.toList}"
