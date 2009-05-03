------------------------------------------------------------------------
-- Some Vec-related properties
------------------------------------------------------------------------

module Data.Vec.Properties where

open import Data.Vec
open import Data.Nat
open import Data.Fin using (Fin; zero; suc)
open import Data.Function
open import Relation.Binary

module UsingVectorEquality (S : Setoid) where

  private module SS = Setoid S
  open SS using () renaming (carrier to A)
  import Data.Vec.Equality as VecEq
  open VecEq.Equality S

  replicate-lemma : ∀ {m} n x (xs : Vec A m) →
                    replicate {n = n}     x ++ (x ∷ xs) ≈
                    replicate {n = 1 + n} x ++      xs
  replicate-lemma zero    x xs = refl (x ∷ xs)
  replicate-lemma (suc n) x xs = SS.refl ∷-cong replicate-lemma n x xs

  xs++[]=xs : ∀ {n} (xs : Vec A n) → xs ++ [] ≈ xs
  xs++[]=xs []       = []-cong
  xs++[]=xs (x ∷ xs) = SS.refl ∷-cong xs++[]=xs xs

open import Relation.Binary.PropositionalEquality

-- lookup is natural.

lookup-natural : ∀ {A B n} (f : A → B) (i : Fin n) →
                 lookup i ∘ map f ≗ f ∘ lookup i
lookup-natural f zero    (x ∷ xs) = refl
lookup-natural f (suc i) (x ∷ xs) = lookup-natural f i xs

-- map is a congruence.

map-cong : ∀ {A B n} {f g : A → B} →
           f ≗ g → _≗_ {Vec A n} (map f) (map g)
map-cong f≗g []       = refl
map-cong f≗g (x ∷ xs) = cong₂ _∷_ (f≗g x) (map-cong f≗g xs)

-- map is functorial.

map-id : ∀ {A n} → _≗_ {Vec A n} (map id) id
map-id []       = refl
map-id (x ∷ xs) = cong (_∷_ x) (map-id xs)

map-∘ : ∀ {A B C n} (f : B → C) (g : A → B) →
        _≗_ {Vec A n} (map (f ∘ g)) (map f ∘ map g)
map-∘ f g []       = refl
map-∘ f g (x ∷ xs) = cong (_∷_ (f (g x))) (map-∘ f g xs)
