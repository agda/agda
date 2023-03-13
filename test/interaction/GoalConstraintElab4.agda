{-# OPTIONS --cubical #-}

open import Agda.Primitive renaming (Set to Type)
open import Agda.Builtin.Cubical.Path
open import Agda.Builtin.Cubical.Glue
open import Agda.Builtin.Cubical.Id
open import Agda.Builtin.Sigma
open import Agda.Primitive.Cubical
  renaming
    ( primIMax to _∨_
    ; primIMin to _∧_
    ; primINeg to ~_
    ; primComp to comp
    ; primHComp to primHComp
    ; primTransp to transp
    ; itIsOne to 1=1
    )

hcomp
  : ∀ {ℓ} {A : Type ℓ} (φ : I)
  → (u : (i : I) → Partial (φ ∨ ~ i) A)
  → A
hcomp φ u = primHComp (λ { j (φ = i1) → u j 1=1 }) (u i0 1=1)

Square : ∀ {ℓ} {A : Type ℓ} {a00 a01 a10 a11 : A}
       → (p : a00 ≡ a01)
       → (q : a00 ≡ a10)
       → (s : a01 ≡ a11)
       → (r : a10 ≡ a11)
       → Type ℓ
Square p q s r = PathP (λ i → p i ≡ r i) q s

∂ : I → I
∂ i = i ∨ ~ i

invert-sides : ∀ {ℓ} {A : Type ℓ} {x y z : A} (p : x ≡ y) (q : x ≡ z)
             → Square q p (λ i → q (~ i)) (λ i → p (~ i))
invert-sides {x = x} p q i j = hcomp (∂ i ∨ ∂ j) λ where
  k (i = i0) → {! p (k ∧ j) !}   -- p (k ∧ j)
  k (i = i1) → {! q (k ∧ ~ j) !} -- q (~ j ∧ k)
  k (j = i0) → {! q (k ∧ i) !}   -- q (i ∧ k)
  k (j = i1) → {! p (k ∧ ~ i) !} -- p (~ i ∧ k)
  k (k = i0) → x           -- x
