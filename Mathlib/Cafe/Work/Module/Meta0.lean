module

import Lean

public def foo (n : Nat) := n + 1

@[expose] public def fooNormal (n : Nat) := n + 1

/-- error: 'meta' theorems are not allowed, 'meta' is a code generation directive -/
#guard_msgs in
meta theorem a : True := trivial
