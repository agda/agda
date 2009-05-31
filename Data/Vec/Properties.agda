------------------------------------------------------------------------
-- Some Vec-related properties
------------------------------------------------------------------------

module Data.Vec.Properties where

open import Algebra
open import Data.Vec
open import Data.Nat
open import Data.Nat.Properties
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

  map-++-commute : ∀ {b n m}(f : b → A)(xs : Vec b n)(ys : Vec b m) →
                   map f (xs ++ ys) ≈ map f xs ++ map f ys
  map-++-commute f []       ys = refl (map f ys)
  map-++-commute f (x ∷ xs) ys = SS.refl ∷-cong map-++-commute f xs ys

import Relation.Binary.PropositionalEquality as PropEq
open PropEq

import Relation.Binary.HeterogeneousEquality as HetEq
open HetEq

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

sum-++-commute : ∀ {n m}(xs : Vec ℕ n)(ys : Vec ℕ m)→ sum (xs ++ ys) ≡ sum xs + sum ys
sum-++-commute []       ys = refl
sum-++-commute (x ∷ xs) ys = begin
  x + sum (xs ++ ys)
    ≡⟨ PropEq.cong (λ p → x + p) (sum-++-commute xs ys) ⟩
  x + (sum xs + sum ys)
    ≡⟨ PropEq.sym (+-assoc x (sum xs) (sum ys)) ⟩
  sum (x ∷ xs) + sum ys
    ∎
  where open ≡-Reasoning
        open CommutativeSemiring commutativeSemiring hiding (_+_ ; sym)


-- foldr-cong

foldr-cong : ∀ {b₁ b₂ : ℕ → Set}{a}{n : ℕ}
             {f₁ : ∀ {n} → a → b₁ n → b₁ (suc n)}
             {f₂ : ∀ {n} → a → b₂ n → b₂ (suc n)}
             {e₁ : b₁ 0}{e₂ : b₂ 0} → 
             (∀ {n}{x}{y₁ : b₁ n} {y₂ : b₂ n} → y₁ ≅ y₂ → f₁ x y₁ ≅ f₂ x y₂) → 
             (e₁ ≅ e₂) →
             (xs : Vec a n) → foldr b₁ f₁ e₁ xs ≅ foldr b₂ f₂ e₂ xs
foldr-cong _        e₁=e₂ []        = e₁=e₂
foldr-cong {b₁} f₁=f₂ e₁=e₂ (x ∷ xs) = f₁=f₂ (foldr-cong {b₁} f₁=f₂ e₁=e₂ xs)

-- foldl-cong 

foldl-cong : ∀ {b₁ b₂ : ℕ → Set}{a}{n : ℕ}
             {f₁ : ∀ {n} → b₁ n → a → b₁ (suc n)}
             {f₂ : ∀ {n} → b₂ n → a → b₂ (suc n)}
             {e₁ : b₁ 0}{e₂ : b₂ 0} →
             (∀ {n}{x}{y₁ : b₁ n}{y₂ : b₂ n} → y₁ ≅ y₂ → f₁ y₁ x ≅ f₂ y₂ x) → 
             (e₁ ≅ e₂) →
             (xs : Vec a n) → foldl b₁ f₁ e₁ xs ≅ foldl b₂ f₂ e₂ xs
foldl-cong _ e₁=e₂ []          = e₁=e₂
foldl-cong {b₁} f₁=f₂ e₁=e₂ (x ∷ xs) =
  foldl-cong {λ n → b₁ (suc n)} f₁=f₂ (f₁=f₂ e₁=e₂) xs

foldr-universal : ∀ {a n}(b : ℕ → Set) →
                  (h : ∀ {n} → Vec a n → b n)
                  (f : ∀ {n} → a → b n → b (suc n)) →  (e : b 0) →
                  (h [] ≡ e) →
                  (∀ {n} x (xs : Vec a n) → h (x ∷ xs) ≡ f x (h xs)) →
                  (xs : Vec a n) → h xs ≡ foldr b f e xs
foldr-universal b h f e base step [] = base
foldr-universal b h f e base step (x ∷ xs) = begin
  h (x ∷ xs)
    ≡⟨ step x xs ⟩
  f x (h xs)
    ≡⟨ PropEq.cong (f x) (foldr-universal b h f e base step xs) ⟩
  f x (foldr b f e xs)
    ∎
  where open ≡-Reasoning

foldr-fusion : ∀ {b c : ℕ → Set}{a}(h : ∀ {n} → b n → c n)
               {f : ∀ {n} → a → b n → b (suc n)}
               {g : ∀ {n} → a → c n → c (suc n)}
               (e : b 0) → 
               (∀ {n} x (y : b n) → h (f x y) ≡ g x (h y)) → 
               ∀ {n} (xs : Vec a n) → (h ∘ foldr b f e) xs ≡ foldr c g (h e) xs
foldr-fusion {b} {c} h {f} {g} e fuse = 
  foldr-universal c (h ∘ foldr b f e) g (h e) refl (λ x xs → fuse x (foldr b f e xs))

idIsFold : ∀ {a n} → (xs : Vec a n) → id xs ≡ foldr (Vec a) _∷_ [] xs
idIsFold {a} = foldr-universal (Vec a) id _∷_ [] refl (λ _ _ → refl)

--


