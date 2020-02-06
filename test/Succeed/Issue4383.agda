{-# OPTIONS --rewriting        #-}
{-# OPTIONS --confluence-check #-}

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

module _ (A : Set) where
  postulate
    D : Set
    f : D → D → D
    r : (x y z : D) → f x (f y z) ≡ f x z

  {-# REWRITE r #-}
  -- WAS:
  -- Confluence check failed: f x (f y (f y₁ z)) reduces to both
  -- f x (f y₁ z) and f x (f y z) which are not equal because
  -- y != y₁ of type D
  -- when checking confluence of the rewrite rule r with itself

  module _ (x y y₁ z : D) where
    -- SUCCEEDS:
    _ : f x (f y₁ z) ≡ f x (f y z)
    _ = refl
