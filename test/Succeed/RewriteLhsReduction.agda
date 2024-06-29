{-# OPTIONS --rewriting #-}

open import Common.Equality

{-# BUILTIN REWRITE _≡_ #-}

postulate
  A : Set
  f g : A → A
  f≡g : ∀ a → f a ≡ g a

{-# REWRITE f≡g  #-}

-- Adding the same rule again would make Agda loop
postulate
  f≡g' : ∀ a → f a ≡ g a
{-# REWRITE f≡g' #-}

goal : ∀ {a} → f a ≡ g a
goal = refl
