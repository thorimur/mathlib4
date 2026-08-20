module

public meta import Lean.Linter.Basic
import Batteries

public meta section

open Lean Elab Command Linter

#check `(term| ⟨1, 2⟩)

def basicLinter : Linter where
  run stx := do
    for stx in stx.topDown do
      if stx.isOfKind ``Lean.Parser.Term.anonymousCtor then
        logWarningAt stx m!"Please never use anonymous constructor notation! You used it for {stx}"

initialize addLinter basicLinter

-- def basicModuleLinter : ModuleLinter where
--   run stxs := do
--     -- logInfo m!"Module linter processing:\n{stxs}"
--     for t in ← getInfoTrees do
--       logInfo m!"{← t. format}"

-- initialize addModuleLinter basicModuleLinter

initialize newConsts : StatefulLinter NameSet (Array (Name × ConstantInfo)) ← do
  registerStatefulLinter (init := {})
    (pre := fun _ prevNames _ => do
      let allNewConsts := (← getEnv).constants.map₂
      let mut newCmdConsts := #[]
      for const in allNewConsts do
        unless prevNames.contains const.1 do
          newCmdConsts := newCmdConsts.push const
      -- logInfo m!"New names: {newCmdConsts.map (MessageData.ofConstName ·.1)}"
      return newCmdConsts)
    (post := fun _ prevNames newCmdConsts? _ _ => do
      let some newCmdConsts := newCmdConsts? | return prevNames
      logInfo m!"Processing previous state: {prevNames.toList.map MessageData.ofConstName}\n\
        With new constants: {newCmdConsts.map (MessageData.ofConstName ·.1)}"
      let mut names := prevNames
      for (name, _) in newCmdConsts do
        names := names.insert name
      if names.size == 3 then throwError "AAAAA!"
      logInfo m!"Total names after this command: {names.toList.map MessageData.ofConstName}"
      return names)

#check Position.getDeclsAfter

initialize badNamespace : StatefulLinter Unit Unit ← do
  registerStatefulLinter (init := ())
    (post := fun _ _ _ _ readIntermediate => do
      let some newNames := readIntermediate newConsts | return
      for (name, info) in newNames do
        let ref ← do
          if let some range ← findDeclarationSyntaxRange? name then
            pure (Syntax.ofRange range)
          else
            getRef
        unless (privateToUserName name).getRoot == `CSLib do
          logInfoAt ref m!"{.ofConstName name} of type {info.type} should start with `CSLib`. Instead, it starts with {(privateToUserName name).getRoot}."
      )
