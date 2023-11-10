{-# OPTIONS --opaque --no-opaque #-}

open import Agda.Builtin.Equality

F : Set₁ → Set₁
F A = A

_ : F Set ≡ Set
_ = refl
