module RewriteExt where

open import Common.Equality

{-# BUILTIN REWRITE _≡_ #-}

postulate
  A B : Set
  f g : A → B
  fx⇢gx : ∀ x → f x ≡ g x

{-# REWRITE fx⇢gx #-}

test : f ≡ g
test = refl

