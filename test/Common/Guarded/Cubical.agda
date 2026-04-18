{-# OPTIONS --cubical --guarded #-}
module Common.Guarded.Cubical where

open import Agda.Primitive
open import Agda.Primitive.Cubical renaming (itIsOne to 1=1)
open import Agda.Primitive.Guarded renaming (löbβ to löbβ-Id)
open import Agda.Builtin.Cubical.Path
open import Common.Guarded.Core
import Common.Equality as Id

private
  variable
    l : Level
    A B : Set l

later-ext : ∀ {A : Set} → {f g : ▹ A} → (▸ \ α → f α ≡ g α) → f ≡ g
later-ext eq = \ i α → eq α i

löbβ : ∀ {l} {A : Set l} → (f : ▹ A → A) → löb f ≡ f (next (löb f))
löbβ f = Id.subst (λ a → löb f ≡ a) (löbβ-Id f) (λ i → löb f)
