

import Lean
-- import Mathlib

/-- info: Task.{u} (α : Type u) : Type u -/
#guard_msgs in
#check Task

variable (t : Task Nat)

/-- info: t.get : Nat -/
#guard_msgs in
#check t.get

-- reference count 0: persistent
-- working on another thread forces the value to be is multithreaded
-- negative references for multithreaded
-- suspicion: reference count mgmt is non-atomic, and you may be reading from a
-- value [note unfinished]
-- fun tangent: ref count overflow in concurrency situation! What if negative refcount underflows to positive?
-- atomic

/--
info: Task.map.{u_1, u_2} {α : Type u_1} {β : Type u_2}
  (f : α → β) (x : Task α)
  (prio : Task.Priority := Task.Priority.default) (sync : Bool := false) : Task β
-/
#guard_msgs (whitespace := lax) in
#check Task.map
/--
info: Task.bind.{u_1, u_2} {α : Type u_1} {β : Type u_2} (x : Task α)
  (f : α → Task β)
  (prio : Task.Priority := Task.Priority.default) (sync : Bool := false) : Task β
-/
#guard_msgs (whitespace := lax) in
#check Task.bind

recall Task.bind {α : Type u_1} {β : Type u_2} (x : Task α) (f : α → Task β) (prio : Task.Priority := Task.Priority.default)
  (sync : Bool := false) : Task β

-- To collect an array of tasks into an array of values, loop over an array composing via bind
-- Generally, don't call get, but...
-- ...Can call `get` if we know task is already complete
-- ...Linking binds will multithread everything moved between the binds. So sometimes we want to eat the cost of sleeping instead. But only in extreme cases; prefer binds and maps.

def Array.getAll (xs : Array (Task α))  : Task (Array α) :=
  Task.mapList (·.toArray) xs.toList


def mapList' (f : List α → β) (tasks : List (Task α)) (prio := Task.Priority.default)
    (sync := false) : Task β :=
  go tasks []
where
  go
    | [], as =>
      if sync then
        .pure <| f as.reverse
      else
        Task.spawn (prio := prio) fun _ => f as.reverse
    | [t], as => t.map (fun a => f (a :: as).reverse) prio sync
    | t::ts, as => t.bind (fun a => go ts (a :: as)) prio sync

def mapList (f : List α → β) (tasks : List (Task α)) (prio := Task.Priority.default)
    (sync := false) : Task β :=
  go tasks []
where
  go
    | [], as =>
      if sync then
        .pure <| f as.reverse
      else
        Task.spawn (prio := prio) fun _ => f as.reverse
    | [t], as => t.map (fun a => f (a :: as).reverse) prio sync
    | t::ts, as => t.bind (fun a => go ts (a :: as)) prio sync

def Array.getAll' (xs : Array (Task α)) (prio := Task.Priority.default) : Task (Array α) :=
  xs.foldl (init := Task.pure #[]) fun xs x =>
    xs.bind (sync := true) (prio := prio) fun xs =>
    x.map (sync := true) (prio := prio) fun x =>
    xs.push x


-- courtesy of Loogle
#check BaseIO.asTask
#check EIO.asTask
#check IO.asTask
#check Std.Async.BaseAsync.asTask
#check Std.Async.EAsync.asTask
#check Lean.Server.ServerTask.BaseIO.asTask
#check Lean.Server.ServerTask.EIO.asTask
#check Lean.Server.ServerTask.IO.asTask
#check Lean.Server.RequestM.asTask
#check Lean.Core.CoreM.asTask
#check Lean.Meta.MetaM.asTask
#check Lean.Elab.Tactic.TacticM.asTask
#check Lean.Elab.Term.TermElabM.asTask



def Array.getAll'' (xs : Array (Task α)) : Task (Array α) :=
  if h : 0 < xs.size then
    go [] xs 0 h
  else
    Task.pure #[]
where
  go (xs : List α) (ts : Array (Task α)) (i : Nat) (h : i < ts.size) :=
    let i' := i+1
    if h : i' < ts.size then
      ts[i].bind (sync := true) fun x =>
        go (x :: xs) ts i' h
    else
      ts[i].map (sync := true) fun x =>
        (x :: xs).foldr (fun x xs => xs.push x) (Array.emptyWithCapacity ts.size)
  decreasing_by ts.size - i

def Promise.race (xs : Array (Task α)) : Task α :=
  -- there's no way for this to be pure.....
  -- surely `Trunc`/`Squash` would work? like we talked last time with random values or uninitialized buffers?
  sorry -- ?

#check IO.Promise

-- t.get := (f (A.get)).get

-- /-- info: IsAtomic.{u_2} (α : Type u_2) [PartialOrder α] [OrderBot α] : Prop -/
-- #guard_msgs in
-- #check IsAtomic

#check Task.spawn (prio := .dedicated) fun _ => 1 + 2

/-- info: (9, 8) -/
#guard_msgs in
#eval (Task.Priority.dedicated, Task.Priority.max)

-- DISCLAIMER: Don't print things in a Task in the language server
-- This will crash the language server (anything that prints to stdout, since
-- stdout is the communication channel between server and client)
-- dbg_trace is fine since it's stderr (but it doesn't print anything)

-- Scheduler: object.cpp
-- hardware concurrency := how many tasks ~ logical cores
-- `LEAN_NUM_THREADS`: environment variable setting the size of the worker pool
-- by default, hardware concurrency; corresponds to how many tasks you want to process at once


class PrintProvider where println : String → BaseIO Unit

export PrintProvider (println)

def withPrintln (x : [PrintProvider] → IO α) : IO α := do
  let ref : IO.Ref (Array (String × Nat)) ← IO.mkRef #[]
  let startTime ← IO.monoNanosNow
  let res ← @x {
    println s := do
      let time ← IO.monoNanosNow
      ref.modify (·.push (s, time))
  }
  for (x, time) in (← ref.get) do
    IO.println s!"At {time - startTime} nanos: {x}"
  return res

open Lean Parser Term in
def optSemicolonTerm : Lean.Parser.Parser := leading_parser
  optSemicolon termParser

open Lean Parser Term in
syntax withPosition("dbg_trace'" term optSemicolonTerm) : term

macro_rules
  | `(dbg_trace' $t:term; $v:term) => do
    `(unsafe unsafeBaseIO (do PrintProvider.println $t; return $v))

run_cmd
  withPrintln do
  let x := 10000 * (← IO.rand 0 5)
  let t := Task.spawn fun _ =>
    let s := Array.range x
    dbg_trace' "Finished array" -- nice workaround
    s
  println s!"Creating array of length {x}"
  println s!"Size of created array: {t.get.size}"


run_cmd
  withPrintln do
  let t ← IO.asTask do
    println "Starting"
    IO.sleep 50
    if ← IO.checkCanceled then
      throw <| .userError s!"Canceled."
    let x := 10000 * (← IO.rand 0 5)
    let s := Array.range x
    println "Finished array"
    return s
  IO.sleep 30
  IO.cancel t
  println s!"Creating array of unknown length"
  println s!"Created array: {t.get.isOk}"


-- literally modelled by a wrapper type
-- ... but not at runtime
/--
info: structure Task.{u} (α : Type u) : Type u
number of parameters: 1
fields:
  Task.get : α
constructor:
  Task.pure.{u} {α : Type u} (get : α) : Task α
-/
#guard_msgs in
#print Task
