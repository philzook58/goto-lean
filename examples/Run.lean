import Increment

#eval v_increment.eval 41 10
#eval v_increment.eval 0xffffffff 10
#eval v_increment.eval 41 0

def main : IO Unit := do
  IO.println (reprStr (v_increment.eval 41 10).1)
