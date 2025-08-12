import Mathlib.Util.Edit.Extension

def Edit.delete (range : String.Range) : Edit where
  range
  replacement := ""

-- In future: need to account for things like code fencing. Should maybe detect by lack of good punctiation at end?
def removeBadNewlines (s : String) (stop : String.Pos := s.endPos) : List Edit := Id.run <| do
  let mut i : String.Pos := 0
  let mut numConsecNewlines := 0
  let mut startConsecNewline : String.Pos := 0
  let mut mostRecentNewline : String.Pos := 0
  let mut edits : List Edit := []
  while i < stop do
    let c := s.get i
    if c == '\n' then
      if numConsecNewlines == 0 then
        startConsecNewline := i
      mostRecentNewline := i
      numConsecNewlines := numConsecNewlines + 1
    else if !c.isWhitespace then
      if !c.isUpper then
        if numConsecNewlines > 1 then
          edits := {
              range := { start := startConsecNewline, stop := mostRecentNewline },
              replacement := ""
            } :: edits
      else
        if numConsecNewlines > 2 then
          edits := {
              range := { start := startConsecNewline, stop := mostRecentNewline },
              replacement := "\n"
            } :: edits
      numConsecNewlines := 0
    i := s.next i
  if numConsecNewlines > 1 then
    edits := {
        range := { start := startConsecNewline, stop := mostRecentNewline },
        replacement := ""
      } :: edits
  return edits.reverse

open Lean Parser Command Syntax

instance : HAdd (String.Range) (String.Pos) (String.Range) where
  hAdd := fun range offset => ⟨range.1 + offset, range.2 + offset⟩

def Edit.shiftEdit (e : Edit) (offset : String.Pos) : Edit :=
  { e with range := e.range + offset }

deriving instance Repr for FileMap

instance : Ord Lean.Position where
  compare p₁ p₂ := compare p₁.line p₂.line |>.then <| compare p₁.column p₂.column

open String in
@[inline] def String.matchAtMostNAux (s : String) (p : Char → Bool) (stopPos : String.Pos)
    (max : Nat) (pos : Pos) : Nat × Pos :=
  if 0 < max then
    if pos < stopPos then
      if p (s.get pos) then
        s.matchAtMostNAux p stopPos (max - 1) (s.next pos)
      else
        (max, pos)
    else if pos = stopPos then
      (max, pos)
    else
      (max + 1, stopPos)
  else (max, pos)

open String in
@[inline] def String.matchBeforeAux (s : String) (p : Char → Bool) (stopPos : Pos)
    (count : Nat) (pos : Pos) : Nat × Pos :=
  if h : pos < stopPos then
    if p (s.get pos) then
      have := Nat.sub_lt_sub_left h (lt_next s pos)
      s.matchBeforeAux p stopPos (count + 1) (s.next pos)
    else
      (count, pos)
  else if pos = stopPos then
    (count, pos)
  else (count - 1, stopPos)
termination_by stopPos.1 - pos.1

def String.matchAtMostN (s : String) (p : Char → Bool) (max : Nat) (startPos : Pos := 0)
    (stopPos : String.Pos := s.endPos) : Pos :=
  (s.matchAtMostNAux p stopPos max startPos).2

def String.matchN? (s : String) (p : Char → Bool) (n : Nat) (startPos : Pos := 0) (stopPos : Pos := s.endPos) :
    Option String.Pos :=
  if n = 0 then
    startPos
  else
    let (remaining, pos) := s.matchAtMostNAux p stopPos n startPos
    if remaining = 0 then some pos else none

def String.match (s : String) (p : Char → Bool) (startPos : Pos := 0) (stopPos : Pos := s.endPos) :
    Nat × String.Pos :=
  s.matchBeforeAux p stopPos 0 startPos

def String.findFromUntil? (s : String) (p : Char → Bool)
    (startPos : String.Pos := 0) (stopPos : String.Pos := s.endPos) : Option String.Pos := Id.run do
  let i := findAux s p stopPos startPos
  if i >= stopPos then return none else return i

def String.findNontrivialStartOfLine? (s : String)
    (startPos : String.Pos := 0) (stopPos := s.endPos) : Option String.Pos := do
  let l ← s.findFromUntil? (· = '\n') startPos stopPos
  return (s.match (· = '\n') l stopPos).2

/-- The first indent after the first (consecutive sequence of) newline(s), given in the form
(numberOfSpaces, ⟨start, stop⟩). -/
def String.findExtraSpaceIndentBySecondLine? (s : String)
    (startPos : String.Pos := 0) (stopPos := s.endPos) : Option (Nat × String.Range) := do
  let l ← s.findNontrivialStartOfLine? startPos stopPos
  let (count, i) ← s.match (· = ' ') l stopPos
  return (count, ⟨l, i⟩)

-- Mainly use `Option` here for nice monadicity. Could just return an empty array.

/-- Produces a sorted nonempty array of edits. -/
def String.dedents? (s : String) (indent : Nat := 0)
    (startPos : String.Pos := 0) (stopPos := s.endPos) : Option (Array Edit) := do
  let (extraIndent, ir) ← s.findExtraSpaceIndentBySecondLine? startPos stopPos
  let dedent := extraIndent - indent
  guard <| 0 < dedent
  let mut i := ir.start
  let mut edits : Array Edit := #[]
  while i < stopPos do
    let some j₀ := s.matchN? (· = ' ') indent (startPos := i) (stopPos := stopPos) | break
    let j₁ := s.matchAtMostN (· = ' ') dedent (startPos := j₀) (stopPos := stopPos)
    if j₀ < j₁ then
      edits := edits.push <| .delete { start := j₀, stop := j₁ }
    let some j₁ := s.findNontrivialStartOfLine? j₁ stopPos | break
    i := j₁
  if edits.isEmpty then none else return edits

def Lean.FileMap.dedents? (map : FileMap) (r : String.Range) (customIndent? : Option Nat := none)
    (dedentFirstLine := false) : Option (Array Edit) := do
  let indent := customIndent?.getD <|
    let (_, indent, endPos) := getFirstLineIndent map r
    if endPos = r.start then indent else 0
  let firstDedent? := if dedentFirstLine then
      let (lineStart, actualIndent, endPos) := getFirstLineIndent map r
      let indent := customIndent?.getD 0
      if indent < actualIndent then
        some (Edit.delete { start := lineStart + ⟨indent⟩, stop := endPos })
      else
        none
    else none
  match firstDedent?, map.source.dedents? indent r.start r.stop with
  | none, a => a
  | some edit, some edits => some (edits.push edit) -- will be sorted by the extension
  | some edit, none => some #[edit]
where
  getFirstLineIndent (map : FileMap) (r : String.Range) : String.Pos × Nat × String.Pos :=
    let lineStart := map.lineStart (map.toPosition r.start).line
    (lineStart, map.source.match (· = ' ') (startPos := lineStart) (stopPos := r.start))

def Lean.FileMap.getLineContents (map : FileMap) (line : Nat) (lastLine := line) : String :=
  map.source.extract (map.lineStart line) (map.lineStart (lastLine + 1))

def Lean.FileMap.getLines (map : FileMap) (range : String.Range) : Nat × Nat :=
  ((map.toPosition range.start).line, (map.toPosition range.stop).line)
