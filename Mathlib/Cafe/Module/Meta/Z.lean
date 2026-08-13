module

import Lean
import all Mathlib.Cafe.Module.Meta.Y


def bazRegular : Nat := 4

public def barRegular (n : Nat) : Bool := n == bazRegular

meta def tPrivateMetaDef! (n : Nat) : Nat := n + (if s n then 4 else 3)
