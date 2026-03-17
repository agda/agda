-- Andreas, 2013-03-20 Problem was that CompiledClause.Match.unfoldCoinduction
-- did not instantiate metas
-- {-# OPTIONS -v tc.meta.assign:10 -v tc.reduce:100 -v tc.with.abstract:50 #-}
{-# OPTIONS --allow-unsolved-metas --guardedness #-}
module Issue826 where

open import Common.Coinduction

postulate
  A : Set
  x : A
  P : A → Set
  p : P x

data Q : ∞ A → Set where

♯x = ♯ x

Foo : Q ♯x
Foo = goal
  where
  x′ : _
  x′ = _ -- problem went away if we wrote ♯x here

  goal : Q x′ -- ensures that x′ = ♯ x (instantiates meta)
  goal = {!♭ x′!} -- normalization of this expression should be x, but was not

  -- Note that ♭ x′ is definitionally equal to x:

  ok : P (♭ x′)
  ok = p

  good : P x
  good with (♭ x′) | p
  good | y | p′ = p′

{- This still does not work because the underscore is solved too late,
   only after with-abstraction is taking place.

  bad : P (♭ x′)
  bad with x | p
  bad | y | p′ = p′

-}
