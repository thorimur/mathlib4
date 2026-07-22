import Lean
structure Foo where
  x : Nat

variable (a : Foo)
run_cmd do
  logInfo m!"{← `(term| a.x)}"

#check Lean.Expr.withApp
