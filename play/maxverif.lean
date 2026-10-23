import play.mymax

#eval run 3 2

def mymax_spec x y := if x > y then x else y

theorem mymax_correct : forall x y, run x y = mymax_spec x y := by
  sorry


/-
Thoughts. yeah,
b0 b1 aren't great.


Locals. It's kind of weird we're being generic via naming convetion?
But really what even would be the point of being more generic?

{
 Locals : Type
 PC : Type

}


lean-iris is intriguing but more confusing than worth?
Since CBMC doesn't natively think in these terms how would you even do it?
Come up with some combinators for reasoning about CBMC state that following seapration logic principles?
I dunno.

ACSL by example.


-/
