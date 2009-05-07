------------------------------------------------------------------------
-- Some Vec-related properties
------------------------------------------------------------------------

module Data.Vec.Properties where

open import Algebra
open import Data.Vec
open import Data.Nat
import Data.Nat.Properties as Nat
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

  map-++-commute : ∀ {B m n} (f : B → A) (xs : Vec B m) {ys : Vec B n} →
                   map f (xs ++ ys) ≈ map f xs ++ map f ys
  map-++-commute f []       = refl _
  map-++-commute f (x ∷ xs) = SS.refl ∷-cong map-++-commute f xs

open import Relation.Binary.PropositionalEquality as PropEq
open import Relation.Binary.HeterogeneousEquality as HetEq

-- lookup is natural.

lookup-natural : ∀ {A B n} (f : A → B) (i : Fin n) →
                 lookup i ∘ map f ≗ f ∘ lookup i
lookup-natural f zero    (x ∷ xs) = refl
lookup-natural f (suc i) (x ∷ xs) = lookup-natural f i xs

-- map is a congruence.

map-cong : ∀ {A B n} {f g : A → B} →
           f ≗ g → _≗_ {Vec A n} (map f) (map g)
map-cong f≗g []       = refl
map-cong f≗g (x ∷ xs) = PropEq.cong₂ _∷_ (f≗g x) (map-cong f≗g xs)

-- map is functorial.

map-id : ∀ {A n} → _≗_ {Vec A n} (map id) id
map-id []       = refl
map-id (x ∷ xs) = PropEq.cong (_∷_ x) (map-id xs)

map-∘ : ∀ {A B C n} (f : B → C) (g : A → B) →
        _≗_ {Vec A n} (map (f ∘ g)) (map f ∘ map g)
map-∘ f g []       = refl
map-∘ f g (x ∷ xs) = PropEq.cong (_∷_ (f (g x))) (map-∘ f g xs)

-- sum commutes with _++_.

sum-++-commute : ∀ {m n} (xs : Vec ℕ m) {ys : Vec ℕ n} →
                 sum (xs ++ ys) ≡ sum xs + sum ys
sum-++-commute []            = refl
sum-++-commute (x ∷ xs) {ys} = begin
  x + sum (xs ++ ys)
    ≡⟨ PropEq.cong (λ p → x + p) (sum-++-commute xs) ⟩
  x + (sum xs + sum ys)
    ≡⟨ PropEq.sym (+-assoc x (sum xs) (sum ys)) ⟩
  sum (x ∷ xs) + sum ys
    ∎
  where
  open ≡-Reasoning
  open CommutativeSemiring Nat.commutativeSemiring hiding (_+_; sym)

-- foldr is a congruence.

foldr-cong : ∀ {A} {B₁} {f₁ : ∀ {n} → A → B₁ n → B₁ (suc n)} {e₁}
                   {B₂} {f₂ : ∀ {n} → A → B₂ n → B₂ (suc n)} {e₂} →
             (∀ {n x} {y₁ : B₁ n} {y₂ : B₂ n} →
                y₁ ≅ y₂ → f₁ x y₁ ≅ f₂ x y₂) →
             e₁ ≅ e₂ →
             ∀ {n} (xs : Vec A n) →
             foldr B₁ f₁ e₁ xs ≅ foldr B₂ f₂ e₂ xs
foldr-cong           _     e₁=e₂ []       = e₁=e₂
foldr-cong {B₁ = B₁} f₁=f₂ e₁=e₂ (x ∷ xs) =
  f₁=f₂ (foldr-cong {B₁ = B₁} f₁=f₂ e₁=e₂ xs)

-- foldl is a congruence.

foldl-cong : ∀ {A} {B₁} {f₁ : ∀ {n} → B₁ n → A → B₁ (suc n)} {e₁}
                   {B₂} {f₂ : ∀ {n} → B₂ n → A → B₂ (suc n)} {e₂} →
             (∀ {n x} {y₁ : B₁ n} {y₂ : B₂ n} →
                y₁ ≅ y₂ → f₁ y₁ x ≅ f₂ y₂ x) →
             e₁ ≅ e₂ →
             ∀ {n} (xs : Vec A n) →
             foldl B₁ f₁ e₁ xs ≅ foldl B₂ f₂ e₂ xs
foldl-cong           _     e₁=e₂ []       = e₁=e₂
foldl-cong {B₁ = B₁} f₁=f₂ e₁=e₂ (x ∷ xs) =
  foldl-cong {B₁ = B₁ ∘₀ suc} f₁=f₂ (f₁=f₂ e₁=e₂) xs

-- The (uniqueness part of the) universality property for foldr.

foldr-universal : ∀ {A} (B : ℕ → Set)
                  (f : ∀ {n} → A → B n → B (suc n)) {e}
                  (h : ∀ {n} → Vec A n → B n) →
                  h [] ≡ e →
                  (∀ {n} x → h ∘ _∷_ x ≗ f {n} x ∘ h) →
                  ∀ {n} → h ≗ foldr B {n} f e
foldr-universal B f     h base step []       = base
foldr-universal B f {e} h base step (x ∷ xs) = begin
  h (x ∷ xs)
    ≡⟨ step x xs ⟩
  f x (h xs)
    ≡⟨ PropEq.cong (f x) (foldr-universal B f h base step xs) ⟩
  f x (foldr B f e xs)
    ∎
  where open ≡-Reasoning

-- A fusion law for foldr.

foldr-fusion : ∀ {A} {B : ℕ → Set} {f : ∀ {n} → A → B n → B (suc n)} e
                     {C : ℕ → Set} {g : ∀ {n} → A → C n → C (suc n)}
               (h : ∀ {n} → B n → C n) →
               (∀ {n} x → h ∘ f {n} x ≗ g x ∘ h) →
               ∀ {n} → h ∘ foldr B {n} f e ≗ foldr C g (h e)
foldr-fusion {B = B} {f} e {C} h fuse =
  foldr-universal C _ _ refl (λ x xs → fuse x (foldr B f e xs))

-- The identity function is a fold.

idIsFold : ∀ {A n} → id ≗ foldr (Vec A) {n} _∷_ []
idIsFold = foldr-universal _ _ id refl (λ _ _ → refl)
