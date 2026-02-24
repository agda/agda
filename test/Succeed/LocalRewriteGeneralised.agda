{-# OPTIONS --rewriting --local-rewriting -WnoRewriteVariablesBoundInSingleton #-}

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

module LocalRewriteGeneralised where

variable
  A B : Set
  x y : A

postulate
  I     : Set
  i0 i1 : I

postulate
  Path : (A : Set) → A → A → Set

-- __IMPOSSIBLE__ in Telescope.hs
module _ {x : A} (f : I → A) (@rew f0 : f i0 ≡ x) where
  test : f i0 ≡ x
  test = refl

-- __IMPOSSIBLE__ in MetaVars.hs
-- module _ (f : I → A) {x y : A}
--          (@rew f0 : f i0 ≡ x) where
--   postulate
--     toPath2 : Path A x y
