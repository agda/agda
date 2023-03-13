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

data Fg (A : Type) : Type where
  inc : A → Fg A
  _◆_ : Fg A → Fg A → Fg A
  inv : Fg A → Fg A
  id  : Fg A
  invl : ∀ x → inv x ◆ x ≡ id
  idl : ∀ x → id ◆ x ≡ x
  assoc : ∀ x y z → (x ◆ y) ◆ z ≡ x ◆ (y ◆ z)

module _
  {A T : Type}
  (f : A → T)
  (m : T → T → T)
  (i : T → T)
  (u : T)
  (il : ∀ x → m (i x) x ≡ u)
  (il : ∀ x → m u x ≡ x)
  (il : ∀ x y z → m (m x y) z ≡ m x (m y z))
  where

  go : Fg A → T
  go (inc x) = f x
  go (x ◆ y) = m (go x) (go y)
  go (inv x) = i (go x)
  go id = u
  go (invl x i) = {!   !}
  go (idl x i) = {!   !}
  go (assoc x x₁ x₂ i) = {!   !}
