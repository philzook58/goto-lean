import Generated

open GotoLean

private def replay (numbers : List Int) : IO String := do
  let n := numbers[0]!.toNat
  let key := BitVec.ofInt 32 numbers[1]!
  let values := numbers.drop 2 |>.map (BitVec.ofInt 32)
  unless values.length == n do throw (IO.userError "bad input length")
  -- Prefix/suffix sentinels also test nonzero offsets and writes outside the array.
  let bytes := #[165, 165, 165, 165] ++
    (values.flatMap (fun v ↦ (Memory.unpack v).toList)).toArray ++ #[90, 90, 90, 90]
  let m : Memory := { objects := #[none, none, some bytes] }
  let p : BitVec 64 := Pointer.make 56 2 4
  let choices := List.replicate (n+4) 0
  let .returned (index, unchanged) := (v_lower_bound.eval p (.ofNat 32 n) key
      (8*(n+1)+6) choices m).1 | throw (IO.userError "search did not return")
  unless unchanged == m do throw (IO.userError "search changed memory")
  let .returned (_, after) := (v_reverse.eval p (.ofNat 32 n)
      (4*(n/2)+3) choices m).1 | throw (IO.userError "reverse did not return")
  let actual := (after.bytes 2).getD #[]
  unless actual[:4].toArray == bytes[:4].toArray &&
      actual[4+4*n:].toArray == bytes[4+4*n:].toArray do
    throw (IO.userError "reverse changed a sentinel")
  let reversed := (List.range n).map (fun i ↦ (Memory.readBits actual (4+4*i) 32).toInt)
  return " ".intercalate (toString index.toNat :: reversed.map toString)

def main : IO Unit := do
  let input ← (← IO.getStdin).readToEnd
  let output ← IO.getStdout
  for line in input.splitOn "\n" do
    if line.trimAscii.toString.isEmpty then continue
    let numbers ← (line.splitOn " ").mapM fun s ↦
      match s.toInt? with
      | some i => pure i
      | none => throw (IO.userError s!"invalid integer: {s}")
    output.putStrLn (← replay numbers)
