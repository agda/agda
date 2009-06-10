------------------------------------------------------------------------
-- Coinductive vectors
------------------------------------------------------------------------

module Data.Covec where

open import Coinduction
open import Data.Nat     using (ℕ; zero; suc)
open import Data.Conat
open import Data.Cofin   using (Cofin; zero; suc)
open import Data.Vec     using (Vec; []; _∷_)
open import Data.Colist as Colist using (Colist; []; _∷_)
open import Data.Product using (_,_)
open import Relation.Binary

------------------------------------------------------------------------
-- The type

infixr 5 _∷_

data Covec (A : Set) : Coℕ → Set where
  []  : Covec A zero
  _∷_ : ∀ {n} (x : A) (xs : ∞ (Covec A (♭ n))) → Covec A (suc n)

------------------------------------------------------------------------
-- Some operations

map : ∀ {A B n} → (A → B) → Covec A n → Covec B n
map f []       = []
map f (x ∷ xs) = f x ∷ ♯ map f (♭ xs)

fromVec : ∀ {A n} → Vec A n → Covec A (fromℕ n)
fromVec []       = []
fromVec (x ∷ xs) = x ∷ ♯ fromVec xs

fromColist : ∀ {A} (xs : Colist A) → Covec A (Colist.length xs)
fromColist []       = []
fromColist (x ∷ xs) = x ∷ ♯ fromColist (♭ xs)

take : ∀ {A} m {n} → Covec A (m + n) → Covec A m
take zero    xs       = []
take (suc n) (x ∷ xs) = x ∷ ♯ take (♭ n) (♭ xs)

drop : ∀ {A} m {n} → Covec A (fromℕ m + n) → Covec A n
drop zero    xs       = xs
drop (suc n) (x ∷ xs) = drop n (♭ xs)

replicate : ∀ {A} n → A → Covec A n
replicate zero    x = []
replicate (suc n) x = x ∷ ♯ replicate (♭ n) x

lookup : ∀ {A n} → Cofin n → Covec A n → A
lookup zero    (x ∷ xs) = x
lookup (suc n) (x ∷ xs) = lookup n (♭ xs)

infixr 5 _++_

_++_ : ∀ {A m n} → Covec A m → Covec A n → Covec A (m + n)
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ ♯ (♭ xs ++ ys)

[_] : ∀ {A} → A → Covec A (suc (♯ zero))
[ x ] = x ∷ ♯ []

------------------------------------------------------------------------
-- Equality and other relations

-- xs ≈ ys means that xs and ys are equal.

infix 4 _≈_

data _≈_ {A} : ∀ {n} (xs ys : Covec A n) → Set where
  []  : [] ≈ []
  _∷_ : ∀ {n} x {xs ys}
        (xs≈ : ∞ (♭ xs ≈ ♭ ys)) → _≈_ {n = suc n} (x ∷ xs) (x ∷ ys)

-- x ∈ xs means that x is a member of xs.

infix 4 _∈_

data _∈_ {A} : ∀ {n} → A → Covec A n → Set where
  here  : ∀ {n x  } {xs}                   → _∈_ {n = suc n} x (x ∷ xs)
  there : ∀ {n x y} {xs} (x∈xs : x ∈ ♭ xs) → _∈_ {n = suc n} x (y ∷ xs)

-- xs ⊑ ys means that xs is a prefix of ys.

infix 4 _⊑_

data _⊑_ {A} : ∀ {m n} → Covec A m → Covec A n → Set where
  []  : ∀ {n} {ys : Covec A n} → [] ⊑ ys
  _∷_ : ∀ {m n} x {xs ys} (p : ∞ (♭ xs ⊑ ♭ ys)) →
        _⊑_ {m = suc m} {suc n} (x ∷ xs) (x ∷ ys)

------------------------------------------------------------------------
-- Some proofs

setoid : Set → Coℕ → Setoid
setoid A n = record
  { carrier       = Covec A n
  ; _≈_           = _≈_
  ; isEquivalence = record
    { refl  = refl
    ; sym   = sym
    ; trans = trans
    }
  }
  where
  refl : ∀ {A n} → Reflexive (_≈_ {A} {n})
  refl {x = []}     = []
  refl {x = x ∷ xs} = x ∷ ♯ refl

  sym : ∀ {A n} → Symmetric (_≈_ {A} {n})
  sym []        = []
  sym (x ∷ xs≈) = x ∷ ♯ sym (♭ xs≈)

  trans : ∀ {A n} → Transitive (_≈_ {A} {n})
  trans []        []         = []
  trans (x ∷ xs≈) (.x ∷ ys≈) = x ∷ ♯ trans (♭ xs≈) (♭ ys≈)

poset : Set → Coℕ → Poset
poset A n = record
  { carrier        = Covec A n
  ; _≈_            = _≈_
  ; _≤_            = _⊑_
  ; isPartialOrder = record
    { isPreorder = record
      { isEquivalence = Setoid.isEquivalence (setoid A n)
      ; reflexive     = reflexive
      ; trans         = trans
      ; ∼-resp-≈      = ((λ {_} → ⊑-resp-≈ˡ) , λ {_} → ⊑-resp-≈ʳ)
      }
    ; antisym  = antisym
    }
  }
  where
  reflexive : ∀ {A n} → _≈_ {A} {n} ⇒ _⊑_
  reflexive []        = []
  reflexive (x ∷ xs≈) = x ∷ ♯ reflexive (♭ xs≈)

  trans : ∀ {A n} → Transitive (_⊑_ {A} {n})
  trans []        _          = []
  trans (x ∷ xs≈) (.x ∷ ys≈) = x ∷ ♯ trans (♭ xs≈) (♭ ys≈)

  ⊑-resp-≈ˡ : ∀ {A n} {xs : Covec A n} →
              (λ ys → xs ⊑ ys) Respects _≈_ {A} {n}
  ⊑-resp-≈ˡ _         []       = []
  ⊑-resp-≈ˡ (x ∷ xs≈) (.x ∷ p) = x ∷ ♯ ⊑-resp-≈ˡ (♭ xs≈) (♭ p)

  ⊑-resp-≈ʳ : ∀ {A n} {ys : Covec A n} →
              (λ xs → xs ⊑ ys) Respects _≈_ {A} {n}
  ⊑-resp-≈ʳ []        _        = []
  ⊑-resp-≈ʳ (x ∷ xs≈) (.x ∷ p) = x ∷ ♯ ⊑-resp-≈ʳ (♭ xs≈) (♭ p)

  antisym : ∀ {A n} → Antisymmetric (_≈_ {A} {n}) _⊑_
  antisym []       []        = []
  antisym (x ∷ p₁) (.x ∷ p₂) = x ∷ ♯ antisym (♭ p₁) (♭ p₂)

map-cong : ∀ {A B n} (f : A → B) → _≈_ {n = n} =[ map f ]⇒ _≈_
map-cong f []        = []
map-cong f (x ∷ xs≈) = f x ∷ ♯ map-cong f (♭ xs≈)

take-⊑ : ∀ {A} m {n} (xs : Covec A (m + n)) → take m xs ⊑ xs
take-⊑ zero    xs       = []
take-⊑ (suc n) (x ∷ xs) = x ∷ ♯ take-⊑ (♭ n) (♭ xs)
