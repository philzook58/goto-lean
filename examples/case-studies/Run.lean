import Generated.Json
import Generated.Slide
import Generated.Lookup

open GotoLean
set_option autoImplicit false

private def returned {w : Nat} : Outcome (BitVec w × Memory) → IO Nat
  | .returned (value, _) => pure value.toNat
  | other => throw (IO.userError (reprStr other))

/-- Same line protocol as native.c; JSON exports every token field and parser state. -/
def main : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  repeat
    let line ← stdin.getLine
    if line.isEmpty then break
    let fields := line.trimAscii.toString.splitOn " "
    let [kind, a, b, c] := fields
      | throw (IO.userError s!"bad input: {line}")
    let values ← [a, b, c].mapM fun text ↦
      match text.toNat? with
      | some n => pure n
      | none => throw (IO.userError s!"bad integer: {text}")
    let [a, b, c] := values | throw (IO.userError "bad arity")
    let choices := List.replicate 1024 0
    let (width, out) ← match kind with
      | "json" => do
        let n ← returned (v_json_case.eval (.ofNat 64 a) (.ofNat 32 b) (.ofNat 32 c)
          1000 choices).fst
        pure (20, n)
      | "slide" => do
        let n ← returned (v_slide_case.eval (.ofNat 32 a) 1000 choices).fst
        pure (1, n)
      | "lookup" => do
        let n ← returned (v_lookup_case.eval (.ofNat 32 a) 1000 choices).fst
        pure (1, n)
      | _ => throw (IO.userError s!"unknown case: {kind}")
    let words := if width == 1 then [out] else
      (List.range width).map (fun i ↦ out / 2^(32*i) % 2^32)
    stdout.putStrLn (String.intercalate " " (words.map toString))
