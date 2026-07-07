{-# OPTIONS --safe #-}

module Issue8587 where

open import Agda.Primitive.Cubical public
open import Agda.Builtin.Unit

bad-path : ∀ {ℓ A} (x y : A) → PathP {ℓ} _ x y
bad-path x y i = y

data ⊥ : Set where

⊥-intro : ⊥
⊥-intro = primTransp (λ i → bad-path ⊤ ⊥ i) i0 tt
