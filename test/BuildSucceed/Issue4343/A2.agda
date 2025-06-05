-- A2 needed for Main, needs A1, poisoned by B1

module A2 where

open import Base
import A1  -- rewrite for a

postulate
  c-is-true : c ≡ true

{-# REWRITE c-is-true #-}

private
  a-is-true : a ≡ true
  a-is-true = refl

  postulate
    f-b-true : f b ≡ true

  {-# REWRITE f-b-true #-}

  thm : f b ≡ true
  thm = refl
