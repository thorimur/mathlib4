module

import Lean

public import Lean.Elab.Command

public meta initialize a : IO.Ref (Option Bool) ←
  IO.eprintln "hello delivered by InitA! "
  IO.mkRef none

initialize normal : IO.Ref (Option Bool) ←
  IO.eprintln "hello delivered by InitA!"
  IO.mkRef none


elab "#foo" : command => Lean.logInfo "hi from initA via foo~"
