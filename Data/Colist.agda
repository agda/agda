------------------------------------------------------------------------
-- Coinductive lists
------------------------------------------------------------------------

module Data.Colist where

open import Coinduction
open import Data.Bool  using (Bool; true; false)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Nat   using (ℕ; zero; suc)
open import Data.Conat
open import Data.List  using (List; []; _∷_)
import Data.BoundedVec.Inefficient as BVec
open BVec using (BoundedVec; []; _∷_)
open import Data.Product using (_,_)
open import Data.Function
open import Relation.Binary

------------------------------------------------------------------------
-- The type

infixr 5 _∷_

data Colist (A : Set) : Set where
  []  : Colist A
  _∷_ : (x : A) (xs : ∞ (Colist A)) → Colist A

------------------------------------------------------------------------
-- Some operations

null : ∀ {A} → Colist A → Bool
null []      = true
null (_ ∷ _) = false

map : ∀ {A B} → (A → B) → Colist A → Colist B
map f []       = []
map f (x ∷ xs) = f x ∷ map′
  where map′ ~ ♯ map f (♭ xs)

fromList : ∀ {A} → List A → Colist A
fromList []       = []
fromList (x ∷ xs) = x ∷ ♯ fromList xs

take : ∀ {A} (n : ℕ) → Colist A → BoundedVec A n
take zero    xs       = []
take (suc n) []       = []
take (suc n) (x ∷ xs) = x ∷ take n (♭ xs)

replicate : ∀ {A} → Coℕ → A → Colist A
replicate zero    x = []
replicate (suc n) x = x ∷ replicate′
  where replicate′ ~ ♯ replicate (♭ n) x

lookup : ∀ {A} → ℕ → Colist A → Maybe A
lookup n       []       = nothing
lookup zero    (x ∷ xs) = just x
lookup (suc n) (x ∷ xs) = lookup n (♭ xs)

infixr 5 _++_

_++_ : ∀ {A} → Colist A → Colist A → Colist A
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ ++′
  where ++′ ~ ♯ (♭ xs ++ ys)

[_] : ∀ {A} → A → Colist A
[ x ] = x ∷ ♯ []

------------------------------------------------------------------------
-- Equality and other relations

-- xs ≈ ys means that xs and ys are equal.

infix 4 _≈_

data _≈_ {A} : (xs ys : Colist A) → Set where
  []  :                                       []     ≈ []
  _∷_ : ∀ x {xs ys} (xs≈ : ∞ (♭ xs ≈ ♭ ys)) → x ∷ xs ≈ x ∷ ys

-- x ∈ xs means that x is a member of xs.

infix 4 _∈_

data _∈_ {A : Set} : A → Colist A → Set where
  here  : ∀ {x   xs}                   → x ∈ x ∷ xs
  there : ∀ {x y xs} (x∈xs : x ∈ ♭ xs) → x ∈ y ∷ xs

-- xs ⊑ ys means that xs is a prefix of ys.

infix 4 _⊑_

data _⊑_ {A : Set} : Colist A → Colist A → Set where
  []  : ∀ {ys}                            → []     ⊑ ys
  _∷_ : ∀ x {xs ys} (p : ∞ (♭ xs ⊑ ♭ ys)) → x ∷ xs ⊑ x ∷ ys

------------------------------------------------------------------------
-- Some proofs

setoid : Set → Setoid
setoid A = record
  { carrier       = Colist A
  ; _≈_           = _≈_
  ; isEquivalence = record
    { refl  = refl
    ; sym   = sym
    ; trans = trans
    }
  }
  where
  refl : Reflexive _≈_
  refl {[]}     = []
  refl {x ∷ xs} = x ∷ refl′
    where refl′ ~ ♯ refl

  sym : Symmetric _≈_
  sym []        = []
  sym (x ∷ xs≈) = x ∷ sym′
    where sym′ ~ ♯ sym (♭ xs≈)

  trans : Transitive _≈_
  trans []        []         = []
  trans (x ∷ xs≈) (.x ∷ ys≈) = x ∷ trans′
    where trans′ ~ ♯ trans (♭ xs≈) (♭ ys≈)

poset : Set → Poset
poset A = record
  { carrier        = Colist A
  ; _≈_            = _≈_
  ; _≤_            = _⊑_
  ; isPartialOrder = record
    { isPreorder = record
      { isEquivalence = Setoid.isEquivalence (setoid A)
      ; reflexive     = reflexive
      ; trans         = trans
      ; ≈-resp-∼      = ((λ {_} → ≈-resp-⊑ˡ) , λ {_} → ≈-resp-⊑ʳ)
      }
    ; antisym  = antisym
    }
  }
  where
  reflexive : _≈_ ⇒ _⊑_
  reflexive []        = []
  reflexive (x ∷ xs≈) = x ∷ reflexive′
    where reflexive′ ~ ♯ reflexive (♭ xs≈)

  trans : Transitive _⊑_
  trans []        _          = []
  trans (x ∷ xs≈) (.x ∷ ys≈) = x ∷ trans′
    where trans′ ~ ♯ trans (♭ xs≈) (♭ ys≈)

  ≈-resp-⊑ˡ : {xs : Colist A} → _≈_ Respects (λ ys → xs ⊑ ys)
  ≈-resp-⊑ˡ _         []       = []
  ≈-resp-⊑ˡ (x ∷ xs≈) (.x ∷ p) = x ∷ ≈-resp-⊑ˡ′
    where ≈-resp-⊑ˡ′ ~ ♯ ≈-resp-⊑ˡ (♭ xs≈) (♭ p)

  ≈-resp-⊑ʳ : {ys : Colist A} → _≈_ Respects (λ xs → xs ⊑ ys)
  ≈-resp-⊑ʳ []        _        = []
  ≈-resp-⊑ʳ (x ∷ xs≈) (.x ∷ p) = x ∷ ≈-resp-⊑ʳ′
    where ≈-resp-⊑ʳ′ ~ ♯ ≈-resp-⊑ʳ (♭ xs≈) (♭ p)

  antisym : Antisymmetric _≈_ _⊑_
  antisym []       []        = []
  antisym (x ∷ p₁) (.x ∷ p₂) = x ∷ antisym′
    where antisym′ ~ ♯ antisym (♭ p₁) (♭ p₂)

map-cong : ∀ {A B} (f : A → B) → _≈_ =[ map f ]⇒ _≈_
map-cong f []        = []
map-cong f (x ∷ xs≈) = f x ∷ map-cong′
  where map-cong′ ~ ♯ map-cong f (♭ xs≈)

take-⊑ : ∀ {A} n (xs : Colist A) →
         let toColist = fromList ∘ BVec.toList in
         toColist (take n xs) ⊑ xs
take-⊑ zero    xs       = []
take-⊑ (suc n) []       = []
take-⊑ (suc n) (x ∷ xs) = x ∷ take-⊑′
  where take-⊑′ ~ ♯ take-⊑ n (♭ xs)
