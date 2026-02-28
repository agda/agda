{-# OPTIONS --rewriting --local-rewriting -WnoRewriteVariablesBoundInSingleton #-}

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

-- Used to hit __IMPOSSIBLE__
-- Now the local rewrites just don't get elaborated because of generalised
-- variables, which still isn't great but at least it doesn't crash
module LocalRewriteGeneralised where

variable
  A B : Set
  x y : A

postulate
  I     : Set
  i0 i1 : I

postulate
  Path : (A : Set) → A → A → Set

-- Used to be __IMPOSSIBLE__ in Telescope.hs
module _ (f : I → A) (@rewrite f0 : f i0 ≡ x) where
  postulate
    test : f i0 ≡ x

-- Used to be __IMPOSSIBLE__ in MetaVars.hs
module _ (f : I → A) {x y : A}
         (@rewrite f0 : f i0 ≡ x) where
  postulate
    test2 : f i0 ≡ x

-- Work-around which doesn't hit any warnings
module _ (f : I → A) {x : A} where
  module _ (@rewrite f0 : f i0 ≡ x) where
    test3 : f i0 ≡ x
    test3 = refl
