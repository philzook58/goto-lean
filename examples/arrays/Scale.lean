import Generated

open GotoLean

private def returned (out : Outcome (α × Memory)) (result : α → Nat) : IO (Nat × Memory) :=
  match out with
  | .returned (r, m) => pure (result r, m)
  | _ => throw (IO.userError "execution failed or exhausted its bound/choices")

private def replay (op : String) (numbers : List Int) : IO String := do
  let n := numbers[0]!.toNat
  let argument := numbers[1]!
  let values := numbers.drop 2 |>.map (BitVec.ofInt 32)
  unless values.length == n && n ≤ 256 do throw (IO.userError "invalid array length")
  let bytes := #[165, 165, 165, 165] ++
    (values.flatMap (fun v ↦ (Memory.unpack v).toList)).toArray ++ #[90, 90, 90, 90]
  let m : Memory := { objects := #[none, none, some bytes] }
  let p : BitVec 64 := Pointer.make 56 2 4
  let length := BitVec.ofNat 32 n
  let choices := List.replicate (if op == "sort" then 2*(n+1)^2+32 else 10*(n+1)+32) 0
  let (r, after) ←
    match op with
    | "fill" =>
      returned (v_fill.eval p length (.ofInt 32 argument) (2*(n+2)) choices m).1 (fun _ ↦ 0)
    | "find" =>
      returned (v_find.eval p length (.ofInt 32 argument) (4*(n+2)) choices m).1 BitVec.toNat
    | "prefix" =>
      returned (v_is_sorted_until.eval p length (4*(n+2)) choices m).1 BitVec.toNat
    | "rotate" =>
      returned (v_rotate.eval p (.ofInt 32 argument) length (32*(n+1)+50) choices m).1 BitVec.toNat
    | "reverse" =>
      returned (v_reverse.eval p length (4*(n+1)+4) choices m).1 (fun _ ↦ 0)
    | "sort" =>
      returned (v_bubble_sort.eval p length (5*((n+1)*(n+2)+2)) choices m).1 (fun _ ↦ 0)
    | _ => throw (IO.userError s!"unknown operation: {op}")
  let actual := (after.bytes 2).getD #[]
  unless actual.size == bytes.size && actual[:4].toArray == bytes[:4].toArray &&
      actual[4+4*n:].toArray == bytes[4+4*n:].toArray do
    throw (IO.userError s!"{op}: changed a sentinel or allocation extent")
  if op == "find" || op == "prefix" then
    unless after == m do throw (IO.userError s!"{op}: changed memory")
  let elements := (List.range n).map (fun i ↦ (Memory.readBits actual (4+4*i) 32).toInt)
  return " ".intercalate (toString r :: elements.map toString)

def main : IO Unit := do
  let input ← (← IO.getStdin).readToEnd
  let output ← IO.getStdout
  for line in input.splitOn "\n" do
    if line.trimAscii.toString.isEmpty then continue
    let op :: fields := line.splitOn " " | throw (IO.userError "missing operation")
    let numbers ← fields.mapM fun s ↦ match s.toInt? with
      | some i => pure i
      | none => throw (IO.userError s!"invalid integer: {s}")
    output.putStrLn (← replay op numbers)
