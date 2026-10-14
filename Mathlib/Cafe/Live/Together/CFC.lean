

#check cfc
-- A "cfc" on `A` lets us turn functions `f : R → R` into functions `A → A`
-- Common goal: write an element `a : A` as some `cfc f a'`, i.e. show/use that it is in the range of `cfc f`

-- Specific to cfc:
-- context such as scalar ring + element; provided by user

-- General:
-- handling sidegoals produced by rewriting (collect all, then solve)
-- do we want to backtrack based on sidegoal solvability?
  -- for certain things essentially unique; but for nonunital cfc, we may have extra sidegoals that are not true and not provable, even though we could first move to unital and it would work


-- Heuristics:
-- move to unital as soon as possible and as "early"
-- likewise for switching scalar rings

/- Approach 1:
Top-down: e.g. for `star a * a`, see `*`, use `cfc_mul`, and create metavariables for arguments that must be rewritten into cfc-form
Look at maximal subexpressions with type `A`, and try to rewrite.
But, need to "see through" `=`, `≤`.

Would also like to target things like norm of `A`, but needs us to be more specific about where


Or:
simp, but collect placeholders. But how?
- maybe: synthetic sorries
- maybe: IO.Ref of mvars

-/

/-
rewrite-with-sidegoals simproc

- somehow need to identify/specify which lemmas are allowed to produce sidegoals
- need to distinguish between which sidegoals are solved "immediately" and which are simply deferred/collected later
- can we bypass the rewrite simproc's need for no metavariables/no increase of metavariable depth

Applicable to:
- `cfc`
- `field_simp`
- `compute_degree`: figure out which lemmas to apply. (can we use )
- `push`/`pull`?
- `measurability`
- `group`
- this gives us rewrite under binders (with sidegoals)
- `ring` etc. ?
- `norm_num` ?


Implementation: instead of new rewrite plugin, would a free variable with an ever-growing metavariable type work?

API for sidegoals:
- sidegoals are hyps with autoparams?
- mdata
- annotation at construction time of simptheorems? attribute?
- dynamically determined depending on what appears in type

Note (Tomas/Arend): code action for inserting `have`.



-/
