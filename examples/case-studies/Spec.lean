import Generated.Init
import GotoLean.MemoryViews
import GotoLean.Termination

/-! Initialization of the pinned upstream jsmn, with all imported pointer checks.
The standalone layout has a parser at object 2, offset 0, and unrelated bytes at object 3.
Parser storage may contain any initial bytes and an arbitrary trailing region. -/
namespace JsmnSpec
open GotoLean

abbrev Bytes := Array (BitVec 8)

def parserAddress : BitVec 64 := Pointer.make 56 2 0

def initialMemory (parserBytes otherBytes : Bytes) : Memory :=
  { objects := #[none, none, some parserBytes, some otherBytes] }

/-- The three C fields: position, next token index, and parent token index. -/
def Initialized (m : Memory) : Prop :=
  m.ValueAt 56 parserAddress (0 : BitVec 32) ∧
  m.ValueAt 56 (Pointer.add 56 parserAddress 4) (0 : BitVec 32) ∧
  m.ValueAt 56 (Pointer.add 56 parserAddress 8) (-1 : BitVec 32)

/-- Every byte outside the 12-byte parser is unchanged, including its trailing region. -/
def Frame (before after : Memory) : Prop :=
  ∀ object offset, object ≠ 2 ∨ 12 ≤ offset →
    after.readByte object offset = before.readByte object offset

/-- For every initial parser contents and unrelated object, initialization safely completes,
sets pos = 0, toknext = 0, toksuper = -1, and preserves all other bytes. -/
def init : Prop :=
  ∀ parserBytes otherBytes : Bytes,
    12 ≤ parserBytes.size → parserBytes.size < 2^64 →
    finishes v_jsmn_init.step 1
      (v_jsmn_init.initial parserAddress (initialMemory parserBytes otherBytes))
      (fun (_, after) ↦ Initialized after ∧ Frame (initialMemory parserBytes otherBytes) after)

end JsmnSpec
