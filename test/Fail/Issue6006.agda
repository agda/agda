{-# OPTIONS --type-in-type --rewriting #-}

infix 10 _≡_

data _≡_ {A : Set} (a : A) : A → Set where
  reflᵉ : a ≡ a

{-# BUILTIN REWRITE _≡_ #-}

postulate
  T : Set
  C : T
  F : T → T

a : T → T
a x = ?

postulate
  r : ∀ x → F (a x) ≡ C

{-# REWRITE r #-}
