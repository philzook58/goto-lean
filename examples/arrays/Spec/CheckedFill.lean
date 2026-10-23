import Checked.Fill
import Spec.Array
import GotoLean.Termination

/-! Reviewable contract for the CBMC-instrumented `upstream/fill.c`.
All six imported pointer properties, plus the model's store check, must succeed.
No fixed array-size or loop-unwinding bound is assumed. -/
namespace ArrayExamples.CheckedSpec
open GotoLean

/-- The accessed object has a representable extent and is not recorded as freed or dead.
These facts describe caller-owned memory, not assumptions inserted into the generated code. -/
structure ObjectState (m : Memory) (p : BitVec 64) : Prop where
  sizeFits : ∀ bytes, m.bytes (Pointer.object 56 p) = some bytes → bytes.size < 2^64
  notDeallocated : Pointer.object 56 p ≠
    Pointer.object 56 (m.getGlobal "__CPROVER_deallocated" (0 : BitVec 64))
  notDead : Pointer.object 56 p ≠
    Pointer.object 56 (m.getGlobal "__CPROVER_dead_object" (0 : BitVec 64))

/-- For every admitted C length and value, instrumented fill safely completes, fills the
array, and preserves surrounding bytes. Empty arrays need no live-object metadata. -/
def fill : Prop :=
  ∀ (base : BitVec 64) (length value : BitVec 32) (before : Memory) (xs : Values),
    WordsAt before base length.toNat xs →
    Pointer.offset 56 base + 4*length.toNat < 2^56 →
    (0 < length.toNat → ObjectState before base) →
    ∃ blocks, finishes v_fill.step blocks (v_fill.initial base length value before)
      (fun (_, after) ↦
        WordsAt after base length.toNat (fun _ ↦ value) ∧ Frame before after base length.toNat)

end ArrayExamples.CheckedSpec
