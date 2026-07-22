module

public import Mathlib.Tactic.Group

/-
b * a ^ m = c * a ^ n

g * g = g ^ 2

Expr level benefits:
- predictability
- coverage
- control
- scoping
- extensibility:
  - downstream
  - monoids too?


/-
- preprocessing step for expansion of commutators, conjugation, etc.
- proof-by-reflection "first normalization" → product of powers in nice expression form
- boundary from nice reflected version → internal representation on meta level
- ringNF normalization of powers + rearrangement
- construct the "ordinary" expression that the proof-by-reflection would "nicely be defeq to", goal
  management

- location mgmt, error mgmt
- v1 features vs. v2 features
- `group_nf` vs. `group` (closing)


Questions
- what to do about (a * b)^100 or (a * b * a⁻¹)^100? a * (b * a⁻¹ * a)^100 a⁻¹
- normal form of ababa?
- (b * a)^100 * b = b * (a * b)^100? How to check these are equal? Maybe by cycling?
  What about only cycling *into* powers? How to make cycling performant? Maybe don't worry for now.
  - What about n'th powers re: cycling?
  - What about expressions with multiple indepedendently-cyclable subexpressions?
- need to import ring hierarchy?
- blowup in size of exponents?
- definitional associativity by embedding in self-hom???
-/

-/


inductive Foo where
| prod : Array Foo →


/-
- cancellation
- inverses
-/

inductive FreeMagma where
| compose : FreeMagma → FreeMagma → FreeMagma
| inv : FreeMagma → FreeMagma
| intPow : FreeMagma → Int → FreeMagma
| natPow : FreeMagma → Nat → FreeMagma
| atom : Nat → FreeMagma -- ?

def eval {α} (atoms : Lean.RArray α) [Group α] : FreeMagma → α
| .compose a b => eval atoms a * eval atoms b
| .inv a => (eval atoms a)⁻¹
| .intPow a n | .natPow a n => (eval atoms a) ^ n
| .atom idx => atoms.get idx

inductive GroupNF where
| mul : GroupNF → Nat → Int → GroupNF
| nil : GroupNF
