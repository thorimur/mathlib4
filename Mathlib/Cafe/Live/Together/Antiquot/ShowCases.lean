module

public meta import Mathlib.Cafe.Live.Together.Antiquot.Attr
-- import Mathlib.Init
import Batteries

open Lean Elab Command Mathlib Parser

#check ParserResolution

elab "#show_stx" t:term : command => logInfo m!"{format t}"
elab "#show_stx" t:command : command => logInfo m!"{format t}"

elab "#show_match_cases " pp:("pp ")? kind:ident : command => do
  let [res] ← liftCoreM <| resolveParserName kind
    | throwErrorAt kind m!"Ambiguous!"
  match res with
  | .category (_cat : Name)
  | .alias (_p : ParserAliasValue) => throwErrorAt kind "Category or alias :/"
  | .parser (decl : Name) (isDescr : Bool) =>
    if isDescr then
      throwErrorAt kind "Descr!"
    let cases := matchGenAttribute.getValues (← getEnv) decl
    if pp.isSome then
      logInfo m!"values: {cases.map (· .top)}"
    else
      logInfo m!"values: {cases.map (· .top |>.map (·.map format))}"

-- elab "#show_match_cases!" : command => do
--   let table ← matchGenAttribute.tableRef.get
--   let e := table.toList.map fun (key, val) => m!"{key} ↦ {val.map fun a => a.value true}"
--   logInfo m!"{(← matchGenAttribute.tableRef.get).map₁.toArray}"
