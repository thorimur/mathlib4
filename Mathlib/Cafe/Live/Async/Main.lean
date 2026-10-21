import Lean

#print Lean.Core.Context

def main : IO Unit := do
  let t ← IO.asTask do
    IO.println "Starting"
    IO.sleep 5000
    if ← IO.checkCanceled then
      throw <| IO.userError s!"Canceled."
    let x := 10000 * (← IO.rand 0 5)
    let s := Array.range x
    dbg_trace "Finished array"
    return s
  IO.sleep 3000
  IO.cancel t
  IO.println s!"Creating array of unknown length"
  IO.println s!"Created array: {t.get.isOk}"
