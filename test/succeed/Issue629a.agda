-- {-# OPTIONS -v tc.meta:30 #-}
{-# OPTIONS --show-implicit --show-irrelevant #-}
module Issue629a where

record ∃ {A : Set} (B : A → Set) : Set where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B proj₁

uncurry : {A : Set} {B : A → Set} {C : ∃ B → Set} →
          ((x : A) (y : B x) → C (x , y)) →
          ((p : ∃ B) → C p)
uncurry f (x , y) = f x y

foo : {A : Set} {B : A → Set} → ∃ B → ∃ B
foo = uncurry λ x y → (x , y)
