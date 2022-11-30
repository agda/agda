{-# OPTIONS --polarity #-}

module _ where

open import Agda.Builtin.Equality

data Right (@- F : @unused Set → Set) (@++ A : Set) : Set where
  construct : (F (Right F A) → A) → Right F A

-- Sample use case

data Mu (@++ F : @++ Set → Set) : Set where
  fix : F (Mu F) → Mu F

data 𝟙 : Set where
  • : 𝟙

infixl 2 _⊎_
infixl 3 _×_
infixl 3 _,_

data _⊎_ (@++ A : Set) (@++ B : Set) : Set where
  inl : A → A ⊎ B
  inr : B → A ⊎ B

record _×_ (@++ A : Set) (@++ B : Set) : Set where
  constructor _,_
  field
    projl : A
    projr : B

ℕ : Set
ℕ = Mu (λ X → 𝟙 ⊎ X)

pattern zero = fix (inl •)
pattern suc n = fix (inr n)

_+_ : ℕ → ℕ → ℕ
zero + a = a
(suc n) + a = suc (n + a)

PolFunList : @++ Set → @++ Set → Set
PolFunList A X = 𝟙 ⊎ A × X

List : @++ Set → Set
List A = Mu (PolFunList A)

pattern nil = fix (inl •)
pattern cons x l = fix (inr (x , l))

_++_ : {A : Set} → List A → List A → List A
nil ++ l = l
(cons x xs) ++ l = cons x (xs ++ l)

hasFmap : (@++ Set → Set) → Set₁
hasFmap F = {A B : Set} → (A → B) → (F A → F B)

{-# TERMINATING #-}
fmapMu : {F F' : @++ Set → Set} → {hasFmap F} → {hasFmap F'} → (∀ X → F X → F' X) → (Mu F → Mu F')
fmapMu {F} {F'} {fmapF} {fmapF'} η (fix x) = fix (fmapF' (fmapMu {F} {F'} {fmapF} {fmapF'} η) (η (Mu F) x))

PolFunListHasFmap : (A : Set) → hasFmap (PolFunList A)
PolFunListHasFmap _ f (inl •) = inl •
PolFunListHasFmap _ f (inr (a , x)) = inr (a , f x)

NatTransPolFunList : {A B : Set} → (A → B) → ∀ X → PolFunList A X → PolFunList B X
NatTransPolFunList f _ (inl •) = inl •
NatTransPolFunList f _ (inr (a , x)) = inr (f a , x)

map : {A B : Set} → (A → B) → (List A → List B)
map {A} {B} f = fmapMu {PolFunList A} {PolFunList B} {PolFunListHasFmap A} {PolFunListHasFmap B} (NatTransPolFunList f)

-- We need this because otherwise pattern synonyms being untyped lead to unsolved metas
-- (and are very slow)
test : let z : ℕ
           z = zero
           s : ℕ → ℕ
           s = suc
           n : List ℕ
           n = nil
           c : ℕ → List ℕ → List ℕ
           c = cons in
           (c (s (s z)) (c (s (s (s z))) n)) ≡ map (λ x → s (s z) + x) (c z (c (s z) n))
test = refl
