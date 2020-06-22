-- Andreas, 2019-04-10, re #3687, better test case for #1926

-- {-# OPTIONS -v interaction.contents.record:20 #-}

module _ (Foo : Set) where

open import Agda.Builtin.Sigma

test : {A : Set} {B : A → Set} (r : Σ A B) → Set
test r = {!r!}  -- C-c C-o
