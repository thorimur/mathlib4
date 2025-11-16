/-
Copyright (c) 2025 Thomas R. Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas R. Murrills
-/
import Lean

/-!
# `end?`

This module provides the command `end?` to assist in closing scopes.

It provides four different clickable options with associated code actions:
1. close the innermost scope
2. close all scopes in a single `end`
3. close all scopes, but close sections in individual `end`s
4. close all scopes individually
-/

open Lean Meta Elab Command Tactic.TryThis

namespace Mathlib.Tactic.EndSuggestion

/--
Given a list of scopes `ends := [n₁, n₂, ... nₙ]` to end, produce a suggestion that suggests
```
end n₁

end n₂

⋮

end nₙ
```
Panics if `ends` is empty.

Adds a newline after `preInfo` before showing it in the infoview, so that all `end`s are aligned.

Makes a code action of the form `s!"{preInfo} {endStr.head!} ⋯ {endStr.getLast!}"`, and omits `⋯`
if there are only two.

Pretty-printing here is a necessary workaround to insert `«»`s appropriately when encountering a
scope that is also a keyword.
-/
private def toSeparateSuggestion (ends : List Name) (preInfo : String) :
    CommandElabM Suggestion := do
  let endStx ← ends.mapM fun h =>
    return SuggestionText.tsyntax (← `(command| end $(mkIdent h)))
  let endStr ← liftCoreM <| endStx.mapM SuggestionText.prettyExtra
  let separated := "\n\n".intercalate endStr
  return {
      suggestion := separated
      preInfo? := preInfo ++ "\n"
      toCodeActionTitle? := if ends.length > 2 then
          some fun _ => s!"{preInfo} {endStr.head!} ⋯ {endStr.getLast!}"
        else if ends.length == 2 then
          some fun _ => s!"{preInfo} {endStr.head!} {endStr.getLast!}"
        else
          none -- use the default
    }

/--
Suggests four different options for closing the currently open scopes:
1. close only the innermost scope
2. close all scopes in a single `end`
3. close all scopes, but close sections in individual `end`s
4. close all scopes individually

When only one scope is open, `end?` only suggests the first option.

When option (3) is the same as either option (2) or (4), `end?` omits it.
-/
elab tk:"end?" : command => do
  let headersAndNamespaces := (← get).scopes.map fun s => (s.header, s.currNamespace)
  if headersAndNamespaces.all (·.1.isEmpty) then
    throwError "No scope is active."
  else
    -- Overkill, but means we don't need to assume any invariants.
    let headersAndNamespaces := headersAndNamespaces.filter (!·.1.isEmpty)
    -- Always suggest ending just the innermost scope.
    let inner := headersAndNamespaces.head!.1
    let inner ← `(command| end $(mkIdent (.mkSimple inner)))
    let mut suggestions : Array Suggestion := #[inner]
    -- Only make other suggestions if we have more than one header.
    if headersAndNamespaces.length > 1 then
      let all := headersAndNamespaces.foldr (init := .anonymous) fun (h,_) n => n.str h
      let allStx ← `(command| end $(mkIdent all))
      suggestions := suggestions.push allStx
      /- List of scope names with section names isolated and namespace components collapsed into a
      single name: -/
      let mut allWithIsolatedSections := []
      let mut nsAcc := Name.anonymous -- full namespace accummulated from root scope
      let mut currNs := Name.anonymous -- namespace component we're currently accummulating
      -- iterate through the `header` of a scope and the current namespace of that scope
      for (header, ns) in headersAndNamespaces.reverse do
        if nsAcc.str header == ns then
          -- `header` comes from a `namespace`; add to the full and current namespace
          nsAcc := nsAcc.str header
          currNs := currNs.str header
        else
          /- `header` is from a `section`; add it by itself, after adding the current namespace
          component being accummulated if present -/
          if !currNs.isAnonymous then
            -- current namespace component is nontrivial, a
            allWithIsolatedSections := (.mkSimple header) :: currNs :: allWithIsolatedSections
          else
            allWithIsolatedSections := (.mkSimple header) :: allWithIsolatedSections
          -- reset the current namespace component after adding a section
          currNs := .anonymous
      if currNs.isAnonymous then allWithIsolatedSections := currNs :: allWithIsolatedSections
      /- Only suggest the sections-isolated version if it will be different from the
      completely-collapsed version and the completely-separated version (detected by counting the
      number of commands). -/
      let n := allWithIsolatedSections.length
      if n > 1 && headersAndNamespaces.length != n then
        let sectionsSeparate ← toSeparateSuggestion allWithIsolatedSections "sections separate:"
        suggestions := suggestions.push sectionsSeparate
      /- Suggest `end foo` `end bar` `end baz` on separate lines for all scopes. -/
      suggestions := suggestions.push <|←
        toSeparateSuggestion (headersAndNamespaces.map (.mkSimple ·.1)) "all separate:"
    -- "Try this:" is just noise in the code action; a leading `end` is sufficient and meaningful.
    liftCoreM <| addSuggestions tk suggestions (codeActionPrefix? := some "")
