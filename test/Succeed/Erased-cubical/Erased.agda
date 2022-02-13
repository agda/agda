{-# OPTIONS --safe --erased-cubical #-}

module Erased-cubical.Erased where

open import Agda.Builtin.Cubical.Glue
open import Agda.Builtin.Cubical.Path
open import Agda.Primitive
open import Agda.Primitive.Cubical

-- Glue can be used in erased contexts.

@0 _ : SSet (lsuc lzero)
_ =
  (φ : I) (A : Set) (B : Partial φ Set)
  (f : PartialP φ (λ x → B x ≃ A)) →
  primGlue A B f

-- Erased higher constructors are allowed.

data ∥_∥ᴱ (A : Set) : Set where
  ∣_∣     : A → ∥ A ∥ᴱ
  @0 trivial : (x y : ∥ A ∥ᴱ) → x ≡ y

-- Non-erased higher constructors are also allowed.

data ∥_∥ (A : Set) : Set where
  ∣_∣     : A → ∥ A ∥
  trivial : (x y : ∥ A ∥) → x ≡ y

-- Modules that use --cubical can be imported.

import Erased-cubical.Cubical as C

-- Definitions from such modules can be used in erased contexts.

@0 _ : {A : Set} → A → C.∥ A ∥
_ = C.∣_∣

-- One can re-export Cubical Agda code using open public.

open import Erased-cubical.Cubical public
  renaming (∥_∥ to ∥_∥ᶜ; ∣_∣ to ∣_∣ᶜ; trivial to trivialᶜ)

-- And also code that uses --without-K.

open import Erased-cubical.Without-K public
