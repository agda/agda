{-# OPTIONS --rewriting --confluence-check -v rewriting:80 #-}

open import Agda.Builtin.Equality

postulate
  decorate      : ∀{a} (A : Set a) → Set a
  rewriteMe     : ∀{a b} {A : Set a} {B : A → Set b}
                → decorate ((x : A) → B x) ≡ (decorate A → ∀ x → decorate (B x))

{-# BUILTIN REWRITE _≡_ #-}
{-# REWRITE rewriteMe #-}

postulate A : Set

test : decorate (A → A) ≡ (decorate A → ∀ (x : A) → decorate A)
test = refl
