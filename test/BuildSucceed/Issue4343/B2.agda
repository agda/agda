-- B2 needed for Main, needs B1, poisoned by A1

module B2 where

open import Base
import B1 -- rewrite for b

postulate
  d-is-true : d ≡ true

{-# REWRITE d-is-true #-}

private
  b-is-true : b ≡ false
  b-is-true = refl

  postulate
    f-a-true : f a ≡ true

  {-# REWRITE f-a-true #-}

  thm : f a ≡ true
  thm = refl
