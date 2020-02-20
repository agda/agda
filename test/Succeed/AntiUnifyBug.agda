-- Jesper, 2019-07-27. Cut down this example from a latent bug in
-- @antiUnify@, which was using @unAbs@ instead of @absBody@.

{-# OPTIONS --double-check #-}

open import Agda.Primitive

postulate
  I : Set
  T : ∀ {p} → Set (lsuc p) → Set (lsuc p)
  t : ∀ {p} → (B : Set (lsuc p)) → (I → I → Set) → B → T B

  x0 : I
  R0 : I → I → Set
  P0 : ∀ p → R0 x0 x0 → Set p
  d0 : R0 x0 x0

  C : ∀ {p} (X : Set) (x : (T (X → Set p))) → Set

  f : ∀ {p} (R : I → I → Set) (P : R x0 x0 → Set p)
    → {{_ : C (R x0 x0) (t (R x0 x0 → Set p) R P)}}
    → (d : R x0 x0) → P d

  instance
    iDP : ∀ {p} → C (R0 x0 x0) (t (R0 x0 x0 → Set p) R0 (P0 p))

fails : ∀ p → P0 p d0
fails p = f _ (P0 p) d0
