# Lean 4 Environment Extensions & Attributes — A Survey

Comprehensive reference for every kind of environment extension and attribute primitive in Lean 4 core, plus curated examples from Batteries and Mathlib illustrating each pattern.

Conventions in this document:

- **Core** links use absolute paths into the local lean4 worktree at `/Users/thomas/.claude-worktrees/lean4/nice-bhabha/src/`.
- **Mathlib** and **Batteries** links are workspace-relative.
- "Persisted" means written into the `.olean` of the file declaring the entry, then re-loaded on import.

---

## At-a-Glance Summary

### Environment extensions

| Kind | Built on | Register | State σ | Persists to OLean | Key interface | Example | Gotcha |
|---|---|---|---|---|---|---|---|
| **EnvExtension σ** | — | test (Lean.Environment:1482) | σ in-memory | nothing | `getState`, `modifyState`, `setState` | (rare; transient state only) | volatile — no OLean roundtrip; almost always wrap with `PersistentEnvExtension` |
| **PersistentEnvExtension α β σ** | `EnvExtension` | registerPersistentEnvExtension (Lean.Environment:1730) | σ + `importedEntries : Array (Array α)` | `Array α` per module (via `exportEntriesFn`, split by `OLeanEntries` level) | `addEntry`, `getState`, `getModuleEntries`, `modifyState` | [@[positivity]](Mathlib/Tactic/Positivity/Core.lean#L108-L121) | `α` (serialized) and `β` (in-memory) decouple — store small data, materialize closures via `addImportedFn` |
| **SimplePersistentEnvExtension α σ** | `PersistentEnvExtension α α (List α × σ)` | registerSimplePersistentEnvExtension (Lean.EnvExtension:44) | `(List α × σ)` | `Array α` | `getEntries`, `getState`, `modifyState` | [@[hint]](Mathlib/Tactic/Hint.lean#L33-L38) | `β = α`; carries both the raw list and your index |
| **TagDeclarationExtension** | `SimplePersistentEnvExtension Name NameSet` | mkTagDeclarationExtension (Lean.EnvExtension:92) | `NameSet` | sorted `Array Name` | `tag`, `isTagged` | (extension layer of `TagAttribute`) | can only tag decls of current module |
| **MapDeclarationExtension α** | `PersistentEnvExtension (Name × α) (Name × α) (NameMap α)` | mkMapDeclarationExtension (Lean.EnvExtension:132) | `NameMap α` | sorted `Array (Name × α)` | `insert`, `find?`, `contains` | [alias info (Batteries)](.lake/packages/batteries/Batteries/Tactic/Alias.lean#L52) | default `asyncMode := .async .mainEnv` (unlike most); default export filters private decls |
| **ScopedEnvExtension α β σ** | `PersistentEnvExtension (Entry α) (Entry β) (StateStack α β σ)` | registerScopedEnvExtension (Lean.ScopedEnvExtension:144) | `StateStack` (mirrors section/namespace stack + active scopes) | `Array (Entry α)`, optionally filtered per level | `addEntry`, `addScopedEntry`, `addLocalEntry`, `addCore`, `getState`, `modifyState` | [@[norm_num]](Mathlib/Tactic/NormNum/Core.lean#L83-L94) | three entry kinds (global / scoped / local); `ofOLeanEntry`/`toOLeanEntry` for α ≠ β |
| **SimpleScopedEnvExtension α σ** | `ScopedEnvExtension α α σ` | registerSimpleScopedEnvExtension (Lean.ScopedEnvExtension:265) | as above | as above | (inherits `ScopedEnvExtension` API) | [@[gcongr]](Mathlib/Tactic/GCongr/Core.lean#L201) | most common choice for namespace-aware tactic lemma sets |
| **LabelExtension** | `SimpleScopedEnvExtension Name (Array Name)` | registerLabelAttr (Lean.LabelAttribute:73) (also registers the user-facing attribute) | `Array Name` (deduplicated) | `Array (Entry Name)` | `labelled : Name → CoreM (Array Name)` | [@[mono]](Mathlib/Tactic/Monotonicity/Attr.lean#L32-L36) | `applicationTime := .afterCompilation`; preferred over `TagAttribute` when scoping is wanted |

### Attributes

| Kind | Built on | Register | State (extension) | Persists | Key interface | Example | Gotcha |
|---|---|---|---|---|---|---|---|
| **AttributeImpl** | — (extends `AttributeImplCore`) | registerBuiltinAttribute (Lean.Attributes:69) | none directly (you bring your own ext) | none directly | `add (decl stx kind) : AttrM Unit`, `erase decl : AttrM Unit` | hand-rolled `add`/`erase` for [@[gcongr]](Mathlib/Tactic/GCongr/Core.lean#L300-L365), [@[norm_num]](Mathlib/Tactic/NormNum/Core.lean#L197-L208) | `erase` defaults to `throwError`; must run inside `(builtin_)initialize`; respects `AttributeApplicationTime` and `AttributeKind` |
| **TagAttribute** | `AttributeImpl` + `PersistentEnvExtension Name Name NameSet` | registerTagAttribute (Lean.Attributes:180) | `NameSet` | sorted `Array Name` | `setTag`, `hasTag` (binary search on imports) | [@[variable_alias]](Mathlib/Tactic/Variable.lean#L105) | no scoping support — use `registerLabelAttr` if you need it |
| **ParametricAttribute α** | `AttributeImpl` + `PersistentEnvExtension (Name × α) (Name × α) (List Name × NameMap α)` | registerParametricAttribute (Lean.Attributes:263) | `(List Name × NameMap α)` | `Array (Name × α)`, optionally order-preserving | `getParam?`, `setParam`, `afterSet` hook | [@[simps]](Mathlib/Tactic/Simps/Basic.lean#L1237-L1249) | one param per decl (errors on overwrite); `preserveOrder := true` disables sorting |
| **EnumAttributes α** | N `AttributeImpl`s sharing one `PersistentEnvExtension (Name × α) (Name × α) (NameMap α)` | registerEnumAttributes (Lean.Attributes:326) | `NameMap α` | sorted `Array (Name × α)` | `getValue`, `setValue` | reducibility / inlining flags in core | N attr names, one ext, one value per decl |
| **LabelAttribute** (`registerLabelAttr`) | wraps a `LabelExtension` | registerLabelAttr (Lean.LabelAttribute:73) | `Array Name` | `Array (Entry Name)` | `labelled` | [@[mono]](Mathlib/Tactic/Monotonicity/Attr.lean#L32-L36) | also see `LabelExtension` row above — this is the attribute-side helper that builds both at once |

---

## Part 1 — Framework Primitives (Lean core)

The mental hierarchy:

```
EnvExtension σ                          -- volatile, in-memory only
└── PersistentEnvExtension α β σ        -- adds OLean export/import (α serialized, β in-memory, σ state)
    ├── SimplePersistentEnvExtension    -- α = β, state is (List α × σ)
    │   ├── TagDeclarationExtension     -- α = Name, σ = NameSet
    │   └── (used by) TagAttribute      -- attribute wrapper
    ├── MapDeclarationExtension α       -- α = (Name × α), σ = NameMap α
    ├── ScopedEnvExtension α β σ        -- global/scoped/local entries with namespace tracking
    │   └── SimpleScopedEnvExtension    -- α = β
    │       └── LabelExtension          -- α = Name, σ = Array Name
    ├── ParametricAttribute α           -- attribute wrapper, α-typed parameter per decl
    └── EnumAttributes α                -- N attribute names sharing one extension
```

Two parallel registries exist:

- **Environment extensions** — registered via `register*EnvExtension*` family. Identified by `Nat` index.
- **Attributes** — registered via `register*Attribute` family or `registerBuiltinAttribute`. Identified by `Name`. An attribute is essentially `AttributeImpl` (`add` / `erase` callbacks) typically *wrapping* an env extension that holds the state.

### 1.1 `EnvExtension σ` — non-persistent base

| | |
|---|---|
| **Defined** | [Lean/Environment.lean:1280](file:///Users/thomas/.claude-worktrees/lean4/nice-bhabha/src/Lean/Environment.lean#L1280) |
| **Built on** | — (primitive) |
| **State** | `σ` — per-environment, in-memory only |
| **Persisted** | Nothing |
| **Register** | `registerEnvExtension (mkInitial : IO σ) (replay? := none) (asyncMode := .mainOnly) : IO (EnvExtension σ)` at Lean.Environment:1482 |
| **Interface** | `getState ext env`, `modifyState ext env f`, `setState ext env s` |
| **Gotchas** | Stored at a `Nat` index in an opaque `Array EnvExtensionState`. Only suitable for transient state — anything you put here vanishes between `lean` invocations. Rarely used directly; almost everything wraps `PersistentEnvExtension`. |

### 1.2 `PersistentEnvExtension α β σ` — the workhorse

| | |
|---|---|
| **Defined** | [Lean/Environment.lean:1598](file:///Users/thomas/.claude-worktrees/lean4/nice-bhabha/src/Lean/Environment.lean#L1598) |
| **Built on** | `EnvExtension (PersistentEnvExtensionState α σ)` where `PersistentEnvExtensionState` bundles `importedEntries : Array (Array α)` and `state : σ` |
| **Type parameters** | `α` = entry type *serialized* into `.olean`; `β` = entry type used during elaboration (may contain closures / `Expr` etc. — does not need to be serializable); `σ` = in-memory state for the current file |
| **Persisted** | `Array α` per module, via `exportEntriesFn : Environment → σ → OLeanEntries (Array α)` |
| **Register** | `registerPersistentEnvExtension (descr : PersistentEnvExtensionDescr α β σ) : IO (PersistentEnvExtension α β σ)` at Lean.Environment:1730. Descriptor at Lean.Environment:1698 has fields `name`, `mkInitial`, `addImportedFn : Array (Array α) → ImportM σ`, `addEntryFn : σ → β → σ`, `exportEntriesFnEx`, `statsFn`, `asyncMode`, `replay?`. |
| **Interface** | `addEntry ext env (b : β)`, `getState ext env : σ`, `modifyState ext env f`, `setState ext env s`, `getModuleEntries ext env modIdx : Array α` |
| **OLean levels** | `OLeanEntries α = { exported : α, server : α, private : α }`. Lets you publish different entries to public consumers vs. server vs. same-module private code. |
| **Import flow** | At module load, `addImportedFn` receives `Array (Array α)` — one inner array per imported module, indexable by `ModuleIdx`. Use `env.getModuleIdxFor? declName` plus `ext.getModuleEntries env idx` for binary-search lookups instead of re-merging into one big map. |
| **Gotchas** | (a) `α` ≠ `β` is the escape hatch: store something small/serializable in `.olean`, materialize it into closures during import. (b) `addImportedFn` runs in `ImportM` so it can read options/environment. (c) Entries should be deterministic in order or sorted, otherwise `.olean` is non-reproducible. (d) `asyncMode` interacts with parallel elaboration — see §1.10. |

### 1.3 `SimplePersistentEnvExtension α σ` — convenience wrapper

| | |
|---|---|
| **Defined** | [Lean/EnvExtension.lean:17](file:///Users/thomas/.claude-worktrees/lean4/nice-bhabha/src/Lean/EnvExtension.lean#L17) |
| **Built on** | `PersistentEnvExtension α α (List α × σ)` — `β` collapsed to `α`, state is a pair of "entries declared this file" and "user-chosen index" |
| **Register** | `registerSimplePersistentEnvExtension (descr : SimplePersistentEnvExtensionDescr α σ) : IO (SimplePersistentEnvExtension α σ)` at Lean.EnvExtension:44. Descriptor wants `addEntryFn : σ → α → σ`, `addImportedFn : Array (Array α) → σ`, `toArrayFn : List α → Array α`. |
| **Interface** | `getEntries ext env : List α`, `getState ext env : σ`, `setState`, `modifyState` |
| **Gotchas** | The `List α` half is the local file's entries, automatically reversed back on export. Use when you want both "the index I built" *and* "the raw list of entries I added in this file" — a common pattern for tactic registries that pre-build a `DiscrTree`. The helper `SimplePersistentEnvExtension.replayOfFilter` at Lean.EnvExtension:38 builds a `replay?` for filter-style state. |

### 1.4 `TagDeclarationExtension` — boolean per-declaration tag

| | |
|---|---|
| **Defined** | [Lean/EnvExtension.lean:90](file:///Users/thomas/.claude-worktrees/lean4/nice-bhabha/src/Lean/EnvExtension.lean#L90) |
| **Built on** | `SimplePersistentEnvExtension Name NameSet` |
| **Persisted** | Sorted `Array Name` |
| **Register** | `mkTagDeclarationExtension (name := by exact decl_name%) (asyncMode := .mainOnly) : IO TagDeclarationExtension` at Lean.EnvExtension:92 |
| **Interface** | `ext.tag env declName : Environment`, `ext.isTagged env declName : Bool` (binary search on imported entries) |
| **Gotchas** | Asserts you only tag declarations defined in the current module (Lean.EnvExtension:115). This is *not* the same as `TagAttribute` — this is just the extension; you'd register a separate attribute that drives it if you wanted user syntax. |

### 1.5 `MapDeclarationExtension α` — `NameMap α` keyed by declaration

| | |
|---|---|
| **Defined** | [Lean/EnvExtension.lean:129](file:///Users/thomas/.claude-worktrees/lean4/nice-bhabha/src/Lean/EnvExtension.lean#L129) |
| **Built on** | `PersistentEnvExtension (Name × α) (Name × α) (NameMap α)` |
| **Persisted** | Sorted `Array (Name × α)` (default `exportEntriesFn` strips private declarations for `.exported` / `.server`) |
| **Register** | `mkMapDeclarationExtension (name := by exact decl_name%) (asyncMode := .async .mainEnv) (exportEntriesFn := …) : IO (MapDeclarationExtension α)` at Lean.EnvExtension:132 |
| **Interface** | `ext.insert env declName val`, `ext.find? env declName : Option α`, `ext.contains env declName : Bool` |
| **Gotchas** | (a) Insertion asserts declaration is from current module. (b) Default `asyncMode` is `.async .mainEnv`, not `.mainOnly` — different from most others. (c) Use this whenever you want "per-declaration metadata that other files need to read" — alias info, `simps` projection data, etc. |

### 1.6 `ScopedEnvExtension α β σ` — global / scoped / local entries

| | |
|---|---|
| **Defined** | [Lean/ScopedEnvExtension.lean:118](file:///Users/thomas/.claude-worktrees/lean4/nice-bhabha/src/Lean/ScopedEnvExtension.lean#L118) |
| **Built on** | `PersistentEnvExtension (Entry α) (Entry β) (StateStack α β σ)` where `Entry α = global α \| scoped Name α` (Lean.ScopedEnvExtension:17) |
| **State** | `StateStack`: a stack of `State σ` (each carrying `activeScopes : NameSet`, `delimitsLocal : Bool`), plus a `ScopedEntries β` map keyed by namespace. The stack mirrors `section`/`namespace` nesting. |
| **Persisted** | `Array (Entry α)`. `exportEntry? : Environment → α → OLeanEntries (Option α)` can filter per OLean level. |
| **Register** | `registerScopedEnvExtension (descr : Descr α β σ) : IO (ScopedEnvExtension α β σ)` at Lean.ScopedEnvExtension:144. Descriptor wants `ofOLeanEntry : σ → α → ImportM β` and `toOLeanEntry : β → α` — i.e. you serialize via `α` but operate via `β`, possibly fancier. |
| **Interface** | `addEntry env b` (global), `addScopedEntry env ns b`, `addLocalEntry env b`, `addCore env b (kind : AttributeKind) (ns : Name)`, `getState env : σ`, `modifyState env f`. Scope management: `pushScope`, `popScope`, `activateScoped ns`. |
| **Gotchas** | (a) The three `AttributeKind`s (`.global` / `.scoped` / `.local`) map directly onto how an entry is stored. (b) Local entries are evicted on `end` of section/namespace. Scoped entries are persisted in the *defining* namespace and only "active" when that namespace is `open`. (c) `finalizeImport : σ → σ` lets you post-process after all imports loaded. |

### 1.7 `SimpleScopedEnvExtension α σ` — convenience

| | |
|---|---|
| **Defined** | [Lean/ScopedEnvExtension.lean:256](file:///Users/thomas/.claude-worktrees/lean4/nice-bhabha/src/Lean/ScopedEnvExtension.lean#L256) |
| **Built on** | `ScopedEnvExtension α α σ` |
| **Register** | `registerSimpleScopedEnvExtension (descr : SimpleScopedEnvExtension.Descr α σ) : IO (SimpleScopedEnvExtension α σ)` at Lean.ScopedEnvExtension:265. Descriptor wants `name`, `addEntry : σ → α → σ`, `initial : σ`, plus optional `finalizeImport`/`exportEntry?`. |
| **Gotchas** | The most common extension type for *tactic lemma sets* (gcongr, push, fun_prop, …) because the OLean format matches the in-memory format and you typically want namespace-aware scoping. |

### 1.8 `LabelExtension` / `registerLabelAttr`

| | |
|---|---|
| **Defined** | [Lean/LabelAttribute.lean:35](file:///Users/thomas/.claude-worktrees/lean4/nice-bhabha/src/Lean/LabelAttribute.lean#L35) (abbreviation `LabelExtension := SimpleScopedEnvExtension Name (Array Name)`) |
| **Register** | `registerLabelAttr (attrName : Name) (attrDescr : String) (ref := by exact decl_name%) : IO LabelExtension` at Lean.LabelAttribute:73. Builds the extension *and* registers an attribute with `AttributeKind`-aware `add`. |
| **Interface** | `labelled (attrName : Name) : CoreM (Array Name)` at Lean.LabelAttribute:95 |
| **Application time** | `.afterCompilation` |
| **Gotchas** | This is the recommended path when you just want "a named bag of declarations users can tag with `@[foo]`" and need namespace/scoping behavior. Distinct from `TagAttribute` (which is `.mainOnly` and doesn't expose scoping). |

### 1.9 Attribute framework — `AttributeImpl` and friends

| | |
|---|---|
| **Defined** | [Lean/Attributes.lean:54](file:///Users/thomas/.claude-worktrees/lean4/nice-bhabha/src/Lean/Attributes.lean#L54) |
| **Structure** | `AttributeImpl extends AttributeImplCore { add : Name → Syntax → AttributeKind → AttrM Unit; erase : Name → AttrM Unit }`. Core fields: `ref` (go-to-def target), `name`, `descr`, `applicationTime`. |
| **`AttributeApplicationTime`** | `.afterTypeChecking` (default), `.afterCompilation`, `.beforeElaboration` — Lean.Attributes:16 |
| **`AttributeKind`** | `.global`, `.local`, `.scoped` — Lean.Attributes:44 |
| **Register** | `registerBuiltinAttribute (attr : AttributeImpl) : IO Unit` at Lean.Attributes:69. Must be called during initialization (`initializing` guard). Stored in `attributeMapRef : IO.Ref (Std.HashMap Name AttributeImpl)`. |
| **Dynamic registration** | The `attributeExtension` at Lean.Attributes:451 is itself a `PersistentEnvExtension` storing `AttributeExtensionOLeanEntry` records. `registerAttributeOfBuilder env builderId ref args : IO Environment` at Lean.Attributes:493 installs a non-builtin attribute from a builder lookup — used by `register_simp_attr`, parser categories, etc. |
| **Gotchas** | (a) `erase` defaults to `throwError`; if you don't override it, `attribute [-foo] x` will fail. (b) `add` runs under `withExporting` iff the target is public. (c) Attribute names must be unique across all of Lean — `registerBuiltinAttribute` throws if you collide. (d) Builtin attributes (those that live in core or are needed before any elaboration) must use `registerBuiltinAttribute` *during `builtin_initialize`* — ordinary `initialize` is too late if you want the attribute available during bootstrap. |

#### `TagAttribute`

| | |
|---|---|
| **Defined** | [Lean/Attributes.lean:175](file:///Users/thomas/.claude-worktrees/lean4/nice-bhabha/src/Lean/Attributes.lean#L175) |
| **Built on** | `AttributeImpl` + `PersistentEnvExtension Name Name NameSet` |
| **Register** | `registerTagAttribute (name) (descr) (validate := fun _ => pure ()) (ref := by exact decl_name%) (applicationTime := …) (asyncMode := .mainOnly) : IO TagAttribute` at Lean.Attributes:180 |
| **Interface** | `attr.setTag decl`, `attr.hasTag env decl` (binary search) |
| **Use** | When you need a *user-facing attribute* (`@[foo]`) that is just a boolean tag, and you don't need scoping. For scoping, use `registerLabelAttr` instead. |

#### `ParametricAttribute α`

| | |
|---|---|
| **Defined** | [Lean/Attributes.lean:242](file:///Users/thomas/.claude-worktrees/lean4/nice-bhabha/src/Lean/Attributes.lean#L242) |
| **Built on** | `AttributeImpl` + `PersistentEnvExtension (Name × α) (Name × α) (List Name × NameMap α)` |
| **Register** | `registerParametricAttribute (impl : ParametricAttributeImpl α) : IO (ParametricAttribute α)` at Lean.Attributes:263. `ParametricAttributeImpl` wants `getParam : Name → Syntax → AttrM α`, `afterSet : Name → α → AttrM Unit`, `preserveOrder : Bool`, `filterExport : Environment → Name → α → Bool`. |
| **Interface** | `attr.getParam? env decl : Option α`, `attr.setParam env decl param : Except String Environment` |
| **Gotchas** | `preserveOrder := true` disables sorting (use when iteration order matters, e.g. precedence). Only one parameter value per declaration — `setParam` errors if you try to overwrite. |

#### `EnumAttributes α`

| | |
|---|---|
| **Defined** | [Lean/Attributes.lean:321](file:///Users/thomas/.claude-worktrees/lean4/nice-bhabha/src/Lean/Attributes.lean#L321) |
| **Built on** | One `PersistentEnvExtension (Name × α) (Name × α) (NameMap α)` shared by many `AttributeImpl`s |
| **Register** | `registerEnumAttributes (attrDescrs : List (Name × String × α)) (validate := …) : IO (EnumAttributes α)` at Lean.Attributes:326 |
| **Interface** | `attrs.getValue env decl`, `attrs.setValue env decl val` |
| **Use** | When you have a small fixed set of mutually-exclusive attributes representing values of an enum (e.g. `@[reducible]` / `@[irreducible]` / `@[default]` for reducibility, or `@[inline]` / `@[inline_if_reduce]` / `@[noinline]` for inlining). N attribute names, one extension, one value per declaration. |

### 1.10 `AsyncMode` — concurrency control

Lean.Environment:1223. Every extension carries an `AsyncMode`:

- `.sync` — blocks reads on the checked environment; fully consistent, but synchronizes against all parallel branches. Safe but slow.
- `.local` — only sees the current branch. Fast; invisible elsewhere.
- `.mainOnly` *(default for most)* — modifications must happen on the main branch; panics otherwise. Best for "I only ever modify this during top-level elaboration."
- `.async branch` — accumulates in the checked env; `get/modify/setState` require an `asyncDecl : Name` so the runtime knows which async branch to consult. Used by extensions like `MapDeclarationExtension` (default `.async .mainEnv`) and `EnumAttributes` because per-declaration metadata is naturally associated with the declaration's own async branch.

`replay?` at Lean.Environment:1273: `(oldState newState : σ) → (newConsts : List Name) → σ → σ` — called when constants are realized asynchronously, so an extension can re-apply changes to a sibling environment.

### 1.11 `OLeanEntries` and import merging

```lean
structure OLeanEntries (α : Type) where
  exported : α   -- visible to all importers
  server   : α   -- additional data the language server needs
  private  : α   -- in-file private metadata, not visible downstream
```

Lean.Environment:1538. `OLeanEntries.uniform : α → OLeanEntries α` (broadcast same data to all levels) is the common case. Splitting matters for things like simp lemma sets that should hide `private` declarations from importers' indices.

`getModuleEntries ext env modIdx (level := .exported)` is the recommended read path when entries are sorted: binary search per module instead of merging everything into one structure on import.

---

## Part 2 — Curated Instances (Batteries & Mathlib)

One representative example per pattern. Many more exist; these are the ones worth reading first.

### Pattern A — Plain tag attribute

| Attribute | Where | Primitive | Stores | Purpose |
|---|---|---|---|---|
| `@[variable_alias]` | [Mathlib/Tactic/Variable.lean:105](Mathlib/Tactic/Variable.lean#L105) | `TagAttribute` | `NameSet` | Marks declarations that `variable?` should expand as aliases |
| `@[mono]` | [Mathlib/Tactic/Monotonicity/Attr.lean:32-36](Mathlib/Tactic/Monotonicity/Attr.lean#L32-L36) | `LabelExtension` (via `register_label_attr`) | `Array Name` | Lemmas the `mono` tactic should try |

Use `registerLabelAttr` (or its `register_label_attr` command sugar) when you want namespace scoping for free; use `registerTagAttribute` only when you genuinely want flat, file-only marking with no scoping.

### Pattern B — Parametric attribute

| Attribute | Where | Primitive | Stores | Purpose |
|---|---|---|---|---|
| `@[simps …]` | [Mathlib/Tactic/Simps/Basic.lean:1237-1249](Mathlib/Tactic/Simps/Basic.lean#L1237-L1249) | `ParametricAttribute (Array Name)` | List of projection names + `NameMap` | Auto-generates projection simp lemmas; the array names the projections to derive |
| `@[algebraize …]` | [Mathlib/Tactic/Algebraize.lean:116](Mathlib/Tactic/Algebraize.lean#L116) | `ParametricAttribute` | Algebraization config | Drives the `algebraize` tactic |

### Pattern C — Scoped lemma collection (SimpleScopedEnvExtension)

The dominant tactic-framework pattern: a `DiscrTree`-backed lemma index that respects namespace scoping.

| Attribute | Where | State (σ) |
|---|---|---|
| `@[gcongr]` | [Mathlib/Tactic/GCongr/Core.lean:201](Mathlib/Tactic/GCongr/Core.lean#L201) | `GCongrLemmas` (head/arity-indexed lemma table) |
| `@[push]` / `@[pull]` | [Mathlib/Tactic/Push/Attr.lean:47](Mathlib/Tactic/Push/Attr.lean#L47), [:80](Mathlib/Tactic/Push/Attr.lean#L80) | `DiscrTree SimpTheorem` / `DiscrTree PullTheorem` |
| `@[fun_prop]` (4 sub-extensions) | [Mathlib/Tactic/FunProp/Theorems.lean:120](Mathlib/Tactic/FunProp/Theorems.lean#L120), [:196](Mathlib/Tactic/FunProp/Theorems.lean#L196), [:228](Mathlib/Tactic/FunProp/Theorems.lean#L228), [:249](Mathlib/Tactic/FunProp/Theorems.lean#L249) | Lambda / Function / Transition / Morphism theorem tables |
| `@[fun_prop_decl]` | [Mathlib/Tactic/FunProp/Decl.lean](Mathlib/Tactic/FunProp/Decl.lean) | `FunPropDecls` |
| `@[trans]` (Batteries) | [.lake/packages/batteries/Batteries/Tactic/Trans.lean:28-33](.lake/packages/batteries/Batteries/Tactic/Trans.lean#L28-L33) | `DiscrTree Name` |

Idiom: store rich, closure-laden lemma entries (e.g. `SimpTheorem`, `GCongrLemma`) directly as `α = β`; the extension serializes the same record into the OLean.

### Pattern D — Cross-file persistent list (SimplePersistentEnvExtension)

For "registries" that don't need namespace scoping but must survive imports.

| Attribute | Where | State |
|---|---|---|
| `@[hint]` | [Mathlib/Tactic/Hint.lean:33-38](Mathlib/Tactic/Hint.lean#L33-L38) | `List (Nat × TSyntax tactic)` — registered hint tactics with priorities |
| `@[env_linter]` (Batteries) | [.lake/packages/batteries/Batteries/Tactic/Lint/Basic.lean:92-99](.lake/packages/batteries/Batteries/Tactic/Lint/Basic.lean#L92-L99) | `NameMap (Name × Bool)` |
| Library notes (Batteries) | [.lake/packages/batteries/Batteries/Util/LibraryNote.lean:52](.lake/packages/batteries/Batteries/Util/LibraryNote.lean#L52) | `Array LibraryNoteEntry` |

### Pattern E — Scoped extension with custom state transform (ScopedEnvExtension)

Use the full `ScopedEnvExtension` (not the `Simple` variant) when `α ≠ β` — i.e. you serialize one thing but materialize a richer in-memory representation on import.

| Attribute | Where | Notes |
|---|---|---|
| `@[norm_num]` | [Mathlib/Tactic/NormNum/Core.lean:83-94](Mathlib/Tactic/NormNum/Core.lean#L83-L94) | `α = Entry`, `β = Entry × NormNumExt`. State is `{ tree: DiscrTree NormNumExt, erased: PHashSet Name }`; the `erased` set lets users `attribute [-norm_num]` a lemma and have the change propagate. |

### Pattern F — Raw PersistentEnvExtension with `addImportedFn`

When you need to rebuild a non-trivial index (e.g. a `DiscrTree`) from imported flat lists.

| Attribute | Where | Stored on import |
|---|---|---|
| `@[positivity]` | [Mathlib/Tactic/Positivity/Core.lean:108-121](Mathlib/Tactic/Positivity/Core.lean#L108-L121) | Rebuilds a `DiscrTree PositivityExt` from `Array Entry` |
| `@[gcongr_forward]` | [Mathlib/Tactic/GCongr/ForwardAttr.lean:30-40](Mathlib/Tactic/GCongr/ForwardAttr.lean#L30-L40) | Forward-reasoning extensions |

### Pattern G — MapDeclarationExtension (per-decl NameMap)

| Attribute / Extension | Where | Stores |
|---|---|---|
| Alias info (Batteries) | [.lake/packages/batteries/Batteries/Tactic/Alias.lean:52](.lake/packages/batteries/Batteries/Tactic/Alias.lean#L52) | `MapDeclarationExtension AliasInfo` (plain / forward / reverse alias) |
| `@[simps]` projection data | [Mathlib/Tactic/Simps/Basic.lean:416-417](Mathlib/Tactic/Simps/Basic.lean#L416-L417) | Per-structure projection metadata |
| Simps notation classes | [Mathlib/Tactic/Simps/NotationClass.lean](Mathlib/Tactic/Simps/NotationClass.lean) | `AutomaticProjectionData` per class |

### Pattern H — User-level command wrappers

Not extensions themselves — they are macros/commands that *instantiate* an extension on demand. These are the surface most library authors interact with.

| Command | Where | Wraps |
|---|---|---|
| `register_simp_attr` (core) | `src/Lean/Meta/Tactic/Simp/SimpTheorems.lean` | Registers a new simp set as a `SimpExtension` |
| `register_label_attr` (core) | Lean.LabelAttribute | `registerLabelAttr` |
| Bulk-registered simp sets | [Mathlib/Tactic/Attr/Register.lean:26-180](Mathlib/Tactic/Attr/Register.lean#L26-L180) | `functor_norm`, `monad_norm`, `parity_simps`, `mfld_simps`, `integral_simps`, `push_end`, `pull_end`, `nontriviality`, `fin_omega`, `ghost_simps`, … |

### Pattern I — Compound (parametric attribute + side-table)

Two extensions cooperating: a `ParametricAttribute` for the user-facing per-decl config, plus a separate persistent table for shared data.

| Attribute | Components |
|---|---|
| `@[to_additive …]` | `ParametricAttribute` for per-decl directives + a persistent `NameMap` translating multiplicative names to additive names. See [Mathlib/Tactic/ToAdditive/Frontend.lean](Mathlib/Tactic/ToAdditive/Frontend.lean) — the translation map needs to be read across files even when the attribute isn't being re-applied. |
| `@[simps]` | `ParametricAttribute (Array Name)` for the projection list + `MapDeclarationExtension` for per-structure projection data ([Simps/Basic.lean:416](Mathlib/Tactic/Simps/Basic.lean#L416)). |

### Pattern J — Hand-rolled `registerBuiltinAttribute`

When `ParametricAttribute` etc. are not flexible enough — usually because you need elaborate validation in `add`, or `erase` behavior, or want to do work at `applicationTime := .afterCompilation`.

| Attribute | Where |
|---|---|
| `@[positivity]` add handler | [Mathlib/Tactic/Positivity/Core.lean:123-148](Mathlib/Tactic/Positivity/Core.lean#L123-L148) |
| `@[gcongr]` add handler | [Mathlib/Tactic/GCongr/Core.lean:300-365](Mathlib/Tactic/GCongr/Core.lean#L300-L365) |
| `@[norm_num]` add+erase | [Mathlib/Tactic/NormNum/Core.lean:197-208](Mathlib/Tactic/NormNum/Core.lean#L197-L208) |
| `@[trans]` add (Batteries) | [.lake/packages/batteries/Batteries/Tactic/Trans.lean:35-51](.lake/packages/batteries/Batteries/Tactic/Trans.lean#L35-L51) |
| `@[env_linter]` add (Batteries) | [.lake/packages/batteries/Batteries/Tactic/Lint/Basic.lean:110-135](.lake/packages/batteries/Batteries/Tactic/Lint/Basic.lean#L110-L135) |

---

## Part 3 — Decision Cheatsheet

| If you need… | Reach for |
|---|---|
| "Did the user tag this decl, yes/no?", file-local only | `registerTagAttribute` |
| Same, but with namespace scoping (`open Foo` activates) | `registerLabelAttr` / `register_label_attr` |
| "Each tagged decl carries an argument" | `registerParametricAttribute` |
| "Small finite set of mutually-exclusive attributes" | `registerEnumAttributes` |
| Per-decl side data needed by other files | `MapDeclarationExtension` (via `mkMapDeclarationExtension`) |
| Lemma index with `DiscrTree` and scope semantics | `SimpleScopedEnvExtension` |
| Lemma index where serialized ≠ in-memory form | `ScopedEnvExtension` (custom `ofOLeanEntry`/`toOLeanEntry`) |
| Big rebuild on import (`DiscrTree` from flat list) | raw `registerPersistentEnvExtension` with custom `addImportedFn` |
| Custom validation/erase behavior | raw `registerBuiltinAttribute` wrapping any of the above |
| Pure user-defined simp set, no Lean-side glue code | `register_simp_attr` command |
| Pure user-defined label set | `register_label_attr` command |

---

## Part 4 — Pitfalls & General Notes

1. **`initialize` vs. `builtin_initialize`.** Attributes used during bootstrap (core, kernel-adjacent) must register in `builtin_initialize`. User code almost always wants plain `initialize`. `registerBuiltinAttribute` enforces `initializing` — calling it outside an init block throws.

2. **`asyncMode` is load-bearing.** Default is `.mainOnly`, which panics if a side branch tries to modify the extension. If you write an extension that gets touched by `realizeConst` (theorem-on-demand) or async elaboration, switch to `.async .mainEnv` and pass `asyncDecl` in queries, or use `.sync` and accept the synchronization cost.

3. **OLean determinism.** Anything that ends up in `exportEntriesFn` is part of the build artifact. Sort entries, avoid `HashMap` iteration order, avoid embedding addresses, or you'll get non-reproducible builds. Most helpers (TagAttribute, ParametricAttribute, EnumAttributes) sort for you; raw `PersistentEnvExtension` does not.

4. **You almost never store `Expr` in `α`.** `Expr` is fine in `β` but goes through `ofOLeanEntry`/`toOLeanEntry` (or a custom `addImportedFn`) for serialization. The exception is `SimpTheorem`-style records that carry preprocessed expressions and accept serialization cost.

5. **Private declarations.** Default `MapDeclarationExtension` filters out private declarations at `.exported` and `.server` levels. If you want them visible (e.g. for in-module-only tooling), supply your own `exportEntriesFn`.

6. **You can only tag declarations from the current module** (`tag`, `insert`, etc. assert this). To tag imported declarations, use scoped/local entries via `ScopedEnvExtension`, or build a separate map keyed on `(declaringModule, name)`.

7. **`AttributeKind.local` ≠ `def local`.** `AttributeKind.local` means "only in current scope, reverts on `end`". A `local def` and a globally-tagged-with-`local`-kind attribute interact only via section scoping — they are independent concepts.

8. **`erase` defaults to error.** Always supply `erase` in `AttributeImpl` if you want `attribute [-foo] x` to work. `ParametricAttribute` and friends don't set one by default either.

9. **`applicationTime`.** `.afterTypeChecking` is the default and almost always correct. Use `.afterCompilation` when you need the compiled code (e.g. inspecting `@[implemented_by]` results). Use `.beforeElaboration` extremely rarely — you don't have a type to look at yet.

10. **Don't construct `EnvExtension` records by hand.** All registrations go through their `register*` functions, which assign a `Nat` index and put the extension into the right global ref. Bypassing them silently breaks `.olean` load/save.

11. **Scoped extensions and `realizeConst`.** Scoped extensions don't currently support `.async` modes well — they assume linear scope-stack operations. If you mix them with theorem-on-demand, expect to need `replay?` plumbing or to redesign as a `MapDeclarationExtension`.

12. **`registerSimpAttr` vs. existing simp sets.** A user-defined simp set is *not* `@[simp]`-but-named — it's a separate `SimpExtension`. The `simp` tactic with `[mySet]` looks them up by name. Don't reach into the global `simpExtension` to add lemmas to "the" simp set under another name; register your own.
