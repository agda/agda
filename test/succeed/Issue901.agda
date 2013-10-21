-- Andreas, 2013-10-21 fixed this issue
-- by refactoring Internal to spine syntax.
module Issue901 where

open import Common.Level

record Ls : Set where
  constructor _,_
  field
    fst : Level
    snd : Level
open Ls

record R (ls : Ls) : Set (lsuc (fst ls ⊔ snd ls)) where
  field
    A : Set (fst ls)
    B : Set (snd ls)

bad : R _
bad = record { A = Set; B = Set₁ }

good : R (_ , _)
good = record { A = Set; B = Set₁ }

{- PROBLEM WAS:

"good" is fine while the body and signature of "bad" are marked in yellow.
Both are fine if we change the parameter of R to not contain levels.

The meta _1 in R _ is never eta-expanded somehow.  I think this
problem will vanish if we let whnf eta-expand metas that are
projected.  E.g.

  fst _1

will result in

  _1 := _2,_3

and then reduce to

  _2

(And that would be easier to implement if Internal was a spine syntax
(with post-fix projections)).  -}
