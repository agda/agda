{-# OPTIONS --cubical --rewriting --confluence-check #-}
open import Agda.Builtin.Cubical.Path using (PathP ; _≡_)
open import Agda.Builtin.Nat renaming (Nat to ℕ; zero to Z; suc to S)
{-# BUILTIN REWRITE _≡_ #-}

_+ℕ_ : ℕ → ℕ → ℕ
x +ℕ Z = x
x +ℕ (S y) = S (x +ℕ y)

+ℕ-id : ∀ x → Z +ℕ x ≡ x
+ℕ-id Z i = Z
+ℕ-id (S x)i  = S (+ℕ-id x i)
{-# REWRITE +ℕ-id #-}
