-- Andreas, 2014-03-02, issue reported by roly.perera
-- Test case by Nisse

{-# OPTIONS --allow-unsolved-metas #-}

-- To see what is going on:
-- {-# OPTIONS -v tc.meta.assign.proj:25 #-}

record Σ (A : Set) (B : A → Set) : Set where
  constructor t
  field
    proj₁ : A
    proj₂ : B proj₁

open Σ public

map : {A B : Set} {P : A → Set} {Q : B → Set} →
      (f : A → B) → (∀ {x} → P x → Q (f x)) →
      Σ A P → Σ B Q
map f g x = t (f (proj₁ x)) (g (proj₂ x))

postulate
  U  : Set
  El : U → Set

mutual

  data C : Set where
    c : (x : C) → (F x → U) → C

  F : C → Set
  F (c x y) = Σ (F x) λ v → El (y v)

f : ∀ x y → F (c x y) → F x
f _ _ = proj₁

postulate
  P : ∀ x y → (F x → F y) → Set
  p : ∀ x y → P (c _ _) (c x y) (map (f _ _) (λ v → v))

-- WAS: internal error in Records.hs
-- NOW: unsolved meta
