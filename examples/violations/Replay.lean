import Generated.Bug_add
import Generated.Fixed_add

-- INT_MAX + 1 fails the imported signed-overflow assertion before arithmetic executes.
#eval (v_bug_add.eval 2147483647 1).1

-- The repair widens before adding, and returns the mathematical result.
#eval (v_fixed_add.eval 2147483647 1).1
