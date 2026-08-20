import Lean
import Batteries
import Batteries.Linter.UnnecessarySeqFocus

/-

## Types of linters

- Syntax
  - `Lean.Elab.Command.Linter`
  - run interactively while editing a file/in a file/during elaboration after each command
  - add (typically) with `initialize addLinter <linter definition>`
  - includes tactic analysis linters
    - registered with `@[tacticAnalysis]`
  - Related:
    - `ModuleLinter`s
    - `StatefulLinter`s
- Environment
  - Two versions of the same thing (being upstreamed):
    - `Linter.EnvLinter.EnvLinter`
    - `Batteries.Tactic.Lint.Linter`
    - run "at the end" via (batteries) `lake exe runLinter` and (core) `lake lint`, which itself may hook into `runLinter`
    - runs on declarations and returns message data
      - To exclude declarations, two options:
        - tag with `@[nolint <linter>]`
        - put in `nolints.json` with `runLinter --update` (`lake lint -- --update`) (true?)
    - add linters to the linter set via `@[env_linter]`
- "Style" text linters for mathlib (edge case!)
  - `Mathlib.Linter.TextBased.TextbasedLinter`
  - Likely to be outmoded by autoformatter
  - Unlikely to be added to unless you're modifying lint-style for mathlib or specific libraries
  - how to extend/add?

-/

open Lean Meta
#check withNewMCtxDepth
#check synthInstance

#check Linter.EnvLinter.EnvLinter
#check Batteries.Tactic.Lint.Linter

open Batteries Tactic



run_meta do
  let s ← saveState
  try
    discard <| pure ()
  catch _ =>
    s.restore
  logInfo m!"{Expr.const ``Bool []} is a type"
