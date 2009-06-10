------------------------------------------------------------------------
-- Coinductive lists
------------------------------------------------------------------------

module Data.Colist where

open import Coinduction
open import Data.Bool          using (Bool; true; false)
open import Data.Maybe         using (Maybe; nothing; just)
open import Data.Nat           using (ℕ; zero; suc)
open import Data.Conat
open import Data.List          using (List; []; _∷_)
open import Data.List.NonEmpty using (List⁺; _∷_)
                               renaming ([_] to [_]⁺)
open import Data.BoundedVec.Inefficient as BVec
  using (BoundedVec; []; _∷_)
open import Data.Product using (_,_)
open import Data.Function
open import Relation.Binary

------------------------------------------------------------------------
-- The type

infixr 5 _∷_

data Colist (A : Set) : Set where
  []  : Colist A
  _∷_ : (x : A) (xs : ∞ (Colist A)) → Colist A

data Any {A} (P : A → Set) : Colist A → Set where
  here  : ∀ {x xs} (px  : P x)          → Any P (x ∷ xs)
  there : ∀ {x xs} (pxs : Any P (♭ xs)) → Any P (x ∷ xs)

data All {A} (P : A → Set) : Colist A → Set where
  []  : All P []
  _∷_ : ∀ {x xs} (px : P x) (pxs : ∞ (All P (♭ xs))) → All P (x ∷ xs)

------------------------------------------------------------------------
-- Some operations

null : ∀ {A} → Colist A → Bool
null []      = true
null (_ ∷ _) = false

length : ∀ {A} → Colist A → Coℕ
length []       = zero
length (x ∷ xs) = suc (♯ length (♭ xs))

map : ∀ {A B} → (A → B) → Colist A → Colist B
map f []       = []
map f (x ∷ xs) = f x ∷ ♯ map f (♭ xs)

fromList : ∀ {A} → List A → Colist A
fromList []       = []
fromList (x ∷ xs) = x ∷ ♯ fromList xs

take : ∀ {A} (n : ℕ) → Colist A → BoundedVec A n
take zero    xs       = []
take (suc n) []       = []
take (suc n) (x ∷ xs) = x ∷ take n (♭ xs)

replicate : ∀ {A} → Coℕ → A → Colist A
replicate zero    x = []
replicate (suc n) x = x ∷ ♯ replicate (♭ n) x

lookup : ∀ {A} → ℕ → Colist A → Maybe A
lookup n       []       = nothing
lookup zero    (x ∷ xs) = just x
lookup (suc n) (x ∷ xs) = lookup n (♭ xs)

infixr 5 _++_

_++_ : ∀ {A} → Colist A → Colist A → Colist A
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ ♯ (♭ xs ++ ys)

concat : ∀ {A} → Colist (List⁺ A) → Colist A
concat []               = []
concat ([ x ]⁺   ∷ xss) = x ∷ ♯ concat (♭ xss)
concat ((x ∷ xs) ∷ xss) = x ∷ ♯ concat (xs ∷ xss)

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
  refl {x ∷ xs} = x ∷ ♯ refl

  sym : Symmetric _≈_
  sym []        = []
  sym (x ∷ xs≈) = x ∷ ♯ sym (♭ xs≈)

  trans : Transitive _≈_
  trans []        []         = []
  trans (x ∷ xs≈) (.x ∷ ys≈) = x ∷ ♯ trans (♭ xs≈) (♭ ys≈)

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
      ; ∼-resp-≈      = ((λ {_} → ⊑-resp-≈ˡ) , λ {_} → ⊑-resp-≈ʳ)
      }
    ; antisym  = antisym
    }
  }
  where
  reflexive : _≈_ ⇒ _⊑_
  reflexive []        = []
  reflexive (x ∷ xs≈) = x ∷ ♯ reflexive (♭ xs≈)

  trans : Transitive _⊑_
  trans []        _          = []
  trans (x ∷ xs≈) (.x ∷ ys≈) = x ∷ ♯ trans (♭ xs≈) (♭ ys≈)

  ⊑-resp-≈ˡ : {xs : Colist A} →  (λ ys → xs ⊑ ys) Respects _≈_
  ⊑-resp-≈ˡ _         []       = []
  ⊑-resp-≈ˡ (x ∷ xs≈) (.x ∷ p) = x ∷ ♯ ⊑-resp-≈ˡ (♭ xs≈) (♭ p)

  ⊑-resp-≈ʳ : {ys : Colist A} →  (λ xs → xs ⊑ ys) Respects _≈_
  ⊑-resp-≈ʳ []        _        = []
  ⊑-resp-≈ʳ (x ∷ xs≈) (.x ∷ p) = x ∷ ♯ ⊑-resp-≈ʳ (♭ xs≈) (♭ p)

  antisym : Antisymmetric _≈_ _⊑_
  antisym []       []        = []
  antisym (x ∷ p₁) (.x ∷ p₂) = x ∷ ♯ antisym (♭ p₁) (♭ p₂)

map-cong : ∀ {A B} (f : A → B) → _≈_ =[ map f ]⇒ _≈_
map-cong f []        = []
map-cong f (x ∷ xs≈) = f x ∷ ♯ map-cong f (♭ xs≈)

take-⊑ : ∀ {A} n (xs : Colist A) →
         let toColist = fromList ∘ BVec.toList in
         toColist (take n xs) ⊑ xs
take-⊑ zero    xs       = []
take-⊑ (suc n) []       = []
take-⊑ (suc n) (x ∷ xs) = x ∷ ♯ take-⊑ n (♭ xs)
