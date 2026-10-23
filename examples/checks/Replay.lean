import Generated.Add

-- A concrete execution: 41 becomes 42. The local declaration consumes one choice.
#eval (v_checked_add.eval 41 1 [0]).1

-- INT_MAX is outside the precondition in checks.c: this path is rejected, not verified.
#eval (v_checked_add.eval 2147483647 1 [0]).1

-- An insufficient execution budget proves nothing about whether the function is safe.
#eval (v_checked_add.eval 41 0 [0]).1
