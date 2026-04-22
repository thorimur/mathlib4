module

public import Lean

open Lean

initialize testExt : PersistentEnvExtension Name (Name × Bool) (NameMap Bool)  ←
  registerPersistentEnvExtension {
    mkInitial := pure {}
    addImportedFn _ := pure {}
    addEntryFn map := fun (n, b) => map.insert n b
    exportEntriesFn map := map.toArray.map fun (n, b) =>
      if b then n ++ `_true else n ++ `_false
  }
