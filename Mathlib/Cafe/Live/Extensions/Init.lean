module

public import Lean
import Batteries

open Lean

public section

#check Environment

#check EnvExtension

#check PersistentEnvExtension.modifyState -- not typical
#check PersistentEnvExtension.addEntry

#check ImportM
#check scopedEnvExtensionsRef

#check Environment

initialize nameLength : PersistentEnvExtension (α := Name × Nat) (β := Name) (σ := NameMap Nat) ← do
  registerPersistentEnvExtension {
    mkInitial : IO (NameMap Nat) := return {}
    addImportedFn imported := do

      let mut s : NameMap Nat := {}
      for (name, length) in imported.flatten do
        s := s.insertIfNew name length
      return s
    addEntryFn map n := map.insertIfNew n n.toString.length
    exportEntriesFn map := map.toArray }

#check ScopedEnvExtension
#check SimplePersistentEnvExtensionDescr
#check SimplePersistentEnvExtension.modifyState

-- #exit

open Elab

private def FOO := true

namespace A

-- @[defeq]
-- theorem foo (a b : Nat) : a = b  := sorry

syntax (name := myAttr) "my_attr " ident : attr

#check ImportM

initialize registerBuiltinAttribute {
  name := `myAttr
  descr := "adds to nameLength"
  applicationTime := .afterCompilation
  add := fun declName stx kind ↦ match stx with
    | `(attr| my_attr $id:ident) => do
      modifyEnv fun env => nameLength.addEntry env (id.getId ++ declName)
    | _ => throwUnsupportedSyntax
  erase _ := pure ()
}

initialize myTagAttr : TagAttribute ← registerTagAttribute `my_tag "simple tag attr"

#check TagAttribute

-- -/
