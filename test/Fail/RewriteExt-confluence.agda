{-# OPTIONS --rewriting --confluence-check #-}


-- Let us assume that extensionality of functions cannot be proved
-- inside "plain" Agda. In that case the code below shows that the
-- REWRITE functionality is not a conservative extension, even if we
-- only use propositional equality as the rewriting relation, and do
-- not use any postulates.

-- Jesper, 2019-05-13: This example is not confluent!

module RewriteExt-confluence where

open import Common.Equality

{-# BUILTIN REWRITE _≡_ #-}

data Unit : Set where
  unit : Unit

module _ {a b} {A : Set a} {B : A → Set b} {f g : (x : A) → B x}
         (f≡g : ∀ x → f x ≡ g x) where

  private

    id : Unit → (x : A) → B x → B x
    id unit _ x = x

    f≡g′ : ∀ u x → id u x (f x) ≡ g x
    f≡g′ unit = f≡g

    {-# REWRITE f≡g′ #-}

    ext′ : ∀ u → (λ x → id u x (f x)) ≡ g
    ext′ u = refl

  ext : f ≡ g
  ext = ext′ unit
