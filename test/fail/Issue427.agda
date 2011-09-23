-- 2011-08-22 Andreas (reported and fixed by Dominique Devriese)
{-# OPTIONS --no-universe-polymorphism #-}
module Issue427 where

data ⊥ : Set where

postulate f : {I : ⊥} (B : _) → ⊥

data A : Set where a : {x y : ⊥} → A 

test : A → Set
test (a {x = x} {y = y}) with f {_}
test (a {x = x} {y = y}) | _ = A
{- old error message:
  ⊥ should be a function type, but it isn't
  when checking that {y} are valid arguments to a function of type ⊥
-}
-- new error message should be: Unresolved metas