
import Lean

/-
# `Decidable`-to-`classical` Linter

This linter suggests replacing `Decidable*` hypotheses which are unused in the type of a theorem with the use of `classical` in the proof.

-/

#check Lean.Elab.Command.State

/-
Possible designs:

## Capture the constant from the environment.
- Disadvantages:
  - can we even easily see which constants have just been added?
  - no access to syntax ranges...

## Traverse the infotrees
- Ugly, but might be the best. A chance to build more infotree infra, I suppose.
- Do we determine whether there is a thing in the hypothesis from the local context there? And then collect forward deps, I suppose. But we want to do it when everything has *finished*, i.e. want to avoid false positives from delayed-assigned mvars which try to depend on everything. What's in the infotree?

Ok, looks like we're traversing the infotrees--especially for correct handling of mutual blocks, I suppose?

We can look for any `CustomInfo` with ``value.typeName == `Lean.Elab.Term.BodyInfo``.
Then
- check the `parentDecl?` in the current context;
- get its type from the environment
- check type, see if prop
- if so, use `isArrow` after telescoping the right amount. Might be faster?

Or
- look at the (always single) `TermInfo` that's a child of `CustomInfo`
- check type of type, see if prop
- look at the local context, find offending instances there (do we have local instances?) by looking at forward dependencies of fvars

Once we find offending instances...how to log them and suggest replacement?

It seems we need to
1. search the infotrees for the binder name? What gives us go-to-def?
2. parse the binders
3. find which one contains the appropriate position range
4. log on/suggest deletion of that

We then want to be able to know where these come from.


Alternatively!

Look at the snap.
```
let some snap := (← read).snap? | throwError "no snap"
let a := snap.new.result!.get.val
logInfo m!"{a.typeName}" -- DefsParsedSnapshot
```

Check if the `binderIds` appear even for instance arguments.


What we need to do:
- for each declaration: test type, to see if
    - it’s a Prop
    - it has a decidable instance argument
- get unnecessary instances (as indices? as fvars?)
- determine the syntactic binders they come from.
    - question: do the types of subordinates declarations always have the parent declaration as a prefix?
        - do they appear as different definitions in the defview? what’s the deal?
        - What should be the spec here? Let’s say the aux theorem’s type depends on it, but the other doesn’t. Well, the warning from the parent is enough. Let’s say the aux has it in its type. Enough to treat it by itself. Let’s say parent has it, neither depends. Well, should only log once, I guess? Well, yes, but both need classical (at once)…
- If in the declaration, mark for deletion. Otherwise suggest omit.
- Can we be smart about `where` and structure instances? Here we have several “bodies”. What shows up in what?
- What about suggesting `open scoped Classical in`?

Some thoughts
Would be great to collect it without opt-in from linter. For now, opt in okay. Maybe a nice way to copy the linter such that it opts in? Also need to catch things emitted by elabs. Would be nice to catch all limiters eventually. RFC perhaps? After proof of usefulness using individual copies

Could be nice to create getBinders, getBody, etc. APIfor parsing declarations. Likewise for assigning elements of local context in info trees to binders behind the api

Info analysis framework that subsumes tactic? Also, better way than passing data via ctx? Just a straight up loop possible, or?

See what’s in Term.State. And importantly, when is it formed?

While checking the full type is good for performance, in the “bad” case we want to maybe recompute in the local context? But which (esp. when dealing with where/matches)? Go for original syntax? Need to get position info for fvarids; possibly just by traversing the info tree until the expr matches. Is there a better way?

likewise, can always find binder syntax just by traversing syntax tree until we find binder syntax which contains the syntax of our type, the latter of which we get from the infotree. but a getBinders API for declaration syntax is nicer!

For inserting classical: Check what bodyStx is for where and top-level matches

QoL: elaborate suggestion in bad case to see if it works, instead of just suggesting to put classical somewhere and waiting for the user to get hit with an error.
-/

#check Lean.Elab.DefsParsedSnapshot

#check Lean.Expr.isArrow

#check Lean.Meta.collectForwardDeps

#check Lean.Elab.TermInfo

set_option trace.Elab.info true

open Lean Meta Elab Command

def x (d : Nat) := True.intro

#check DefKind.isTheorem
def n := `decidableToClassical

#check CustomInfo
def Lean.Elab.Info.isCustomInfoOf (n : Name) : Info → Bool
| .ofCustomInfo { stx .. } => stx.getKind == n
| _ => false


def Lean.Syntax.isOriginal (stx : Syntax) : Bool := Id.run do
  for stx in stx.topDown do
    if stx matches .node .. then continue
    let some info := stx.getInfo? | return false
    match info with
    | .original .. => continue
    | _ => return false
  return true

def InfoT (m : Type → Type) := ReaderT

#check mkDefView
deriving instance TypeName for HeaderProcessedSnapshot

#check InfoTree.node
def run : Linter where
  name := n
  run stx := do
    let some snap := (← read).snap? | throwError "no snap"
    let a := snap.new.result!.get.val
      -- | logInfo m!"not a HeaderProcessedSnapshot"
    logInfo m!"{a.typeName}"
    -- logInfo m!"The ctx.snap? is some: {(← read).snap?.map}"
    if (← get).snapshotTasks.isEmpty then logInfo "no snaps"
    for task in (← get).snapshotTasks do
      logSnapshotTask task
    let trees ← getInfoTrees
    for t in trees do
      let some as ← t.visitM (postNode := fun ctx i ch as => do
          let as := as.reduceOption.flatten
          match i with
          | .ofCustomInfo { stx, value } =>
            if value.typeName == ``Term.BodyInfo then
              let val := value.get? (α := Lean.Elab.Term.BodyInfo) |>.bind (·.value?)
              let fmt : Format ← match val with
                | some v => liftCoreM do (Meta.ppExpr v).run' {  } { mctx := ctx.mctx }
                | none => pure f!"<no expr>"
              let cinfo ← getConstInfo ctx.parentDecl?.get!

              return f!"{ctx.parentDecl?}{ch.size} {cinfo.type} {value.typeName}: [{fmt}]\n{stx}" :: as
            else return as
          | _ => return as)
        | logInfo "none found"
      logInfo m!"{as}"
      let some as ← t.visitM (postNode := fun ctx i ch as => do
          let as := as.reduceOption.flatten
          match i with
          | .ofTermInfo { stx .. } =>
            if stx.isOriginal then return f!"{stx}" :: as else return as
          | _ => return as)
        | logInfo "none found"
      logInfo m!"{as}"

run_cmd do
  lintersRef.modify fun ls => ls.eraseP (·.name == n)
  addLinter run


#check mkDefView

set_option trace.Elab.info true

variable (q : String)

#check ConstantInfo

mutual

def foo {α} [DecidableEq α] (a b : α) : Nat → ∀ x : Unit, a = a
| n => fun _ => rfl
where
  go (d : False) : True := True.intro

def r := true

opaque cc : True

end

inductive Foo {α} [DecidableEq α] where
| x
