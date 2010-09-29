------------------------------------------------------------------------
-- Coinductive lists
------------------------------------------------------------------------

{-# OPTIONS --universe-polymorphism #-}
module Data.Colist where

open import Category.Monad
open import Coinduction
open import Data.Bool          using (Bool; true; false)
open import Data.Empty         using (⊥)
open import Data.Maybe         using (Maybe; nothing; just)
open import Data.Nat           using (ℕ; zero; suc)
open import Data.Conat         using (Coℕ; zero; suc)
open import Data.List          using (List; []; _∷_)
open import Data.List.NonEmpty using (List⁺; _∷_)
                               renaming ([_] to [_]⁺)
open import Data.BoundedVec.Inefficient as BVec
  using (BoundedVec; []; _∷_)
open import Data.Product using (_,_)
open import Data.Sum     using (_⊎_; inj₁; inj₂)
open import Function
open import Level
open import Relation.Binary
import Relation.Binary.InducedPreorders as Ind
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary
open import Relation.Nullary.Negation
open RawMonad ¬¬-Monad

------------------------------------------------------------------------
-- The type

infixr 5 _∷_

data Colist {ℓ} (A : Set ℓ) : Set ℓ where
  []  : Colist A
  _∷_ : (x : A) (xs : ∞ (Colist A)) → Colist A

data Any {ℓ ℓ′} {A : Set ℓ} (P : A → Set ℓ′) : Colist A → Set (ℓ ⊔ ℓ′) where
  here  : ∀ {x xs} (px  : P x)          → Any P (x ∷ xs)
  there : ∀ {x xs} (pxs : Any P (♭ xs)) → Any P (x ∷ xs)

data All {ℓ ℓ′} {A : Set ℓ} (P : A → Set ℓ′) : Colist A → Set (ℓ ⊔ ℓ′) where
  []  : All P []
  _∷_ : ∀ {x xs} (px : P x) (pxs : ∞ (All P (♭ xs))) → All P (x ∷ xs)

------------------------------------------------------------------------
-- Some operations

null : ∀ {ℓ} {A : Set ℓ} → Colist A → Bool
null []      = true
null (_ ∷ _) = false

length : ∀ {ℓ} {A : Set ℓ} → Colist A → Coℕ
length []       = zero
length (x ∷ xs) = suc (♯ length (♭ xs))

map : ∀ {ℓ} {A B : Set ℓ} → (A → B) → Colist A → Colist B
map f []       = []
map f (x ∷ xs) = f x ∷ ♯ map f (♭ xs)

fromList : ∀ {ℓ} {A : Set ℓ} → List A → Colist A
fromList []       = []
fromList (x ∷ xs) = x ∷ ♯ fromList xs

take : ∀ {ℓ} {A : Set ℓ} (n : ℕ) → Colist A → BoundedVec A n
take zero    xs       = []
take (suc n) []       = []
take (suc n) (x ∷ xs) = x ∷ take n (♭ xs)

replicate : ∀ {ℓ} {A : Set ℓ} → Coℕ → A → Colist A
replicate zero    x = []
replicate (suc n) x = x ∷ ♯ replicate (♭ n) x

lookup : ∀ {ℓ} {A : Set ℓ} → ℕ → Colist A → Maybe A
lookup n       []       = nothing
lookup zero    (x ∷ xs) = just x
lookup (suc n) (x ∷ xs) = lookup n (♭ xs)

infixr 5 _++_

_++_ : ∀ {ℓ} {A : Set ℓ} → Colist A → Colist A → Colist A
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ ♯ (♭ xs ++ ys)

concat : ∀ {ℓ} {A : Set ℓ} → Colist (List⁺ A) → Colist A
concat []               = []
concat ([ x ]⁺   ∷ xss) = x ∷ ♯ concat (♭ xss)
concat ((x ∷ xs) ∷ xss) = x ∷ ♯ concat (xs ∷ xss)

[_] : ∀ {ℓ} {A : Set ℓ} → A → Colist A
[ x ] = x ∷ ♯ []

------------------------------------------------------------------------
-- Equality

-- xs ≈ ys means that xs and ys are equal.

infix 4 _≈_

data _≈_ {ℓ} {A : Set ℓ} : (xs ys : Colist A) → Set ℓ where
  []  :                                       []     ≈ []
  _∷_ : ∀ x {xs ys} (xs≈ : ∞ (♭ xs ≈ ♭ ys)) → x ∷ xs ≈ x ∷ ys

-- The equality relation forms a setoid.

setoid : ∀ {ℓ} → Set ℓ → Setoid _ _
setoid A = record
  { Carrier       = Colist A
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

module ≈-Reasoning where
  import Relation.Binary.EqReasoning as EqR
  private
    open module R {ℓ} {A : Set ℓ} = EqR (setoid A) public

-- map preserves equality.

map-cong : ∀ {ℓ} {A B : Set ℓ} (f : A → B) → _≈_ =[ map f ]⇒ _≈_
map-cong f []        = []
map-cong f (x ∷ xs≈) = f x ∷ ♯ map-cong f (♭ xs≈)

------------------------------------------------------------------------
-- Memberships, subsets, prefixes

-- x ∈ xs means that x is a member of xs.

infix 4 _∈_

_∈_ : ∀ {ℓ} → {A : Set ℓ} → A → Colist A → Set ℓ
x ∈ xs = Any (_≡_ x) xs

-- xs ⊆ ys means that xs is a subset of ys.

infix 4 _⊆_

_⊆_ : ∀ {ℓ} → {A : Set ℓ} → Colist A → Colist A → Set ℓ
xs ⊆ ys = ∀ {x} → x ∈ xs → x ∈ ys

-- xs ⊑ ys means that xs is a prefix of ys.

infix 4 _⊑_

data _⊑_ {ℓ} {A : Set ℓ} : Colist A → Colist A → Set ℓ where
  []  : ∀ {ys}                            → []     ⊑ ys
  _∷_ : ∀ x {xs ys} (p : ∞ (♭ xs ⊑ ♭ ys)) → x ∷ xs ⊑ x ∷ ys

-- Prefixes are subsets.

⊑⇒⊆ : ∀ {ℓ} → {A : Set ℓ} → _⊑_ {A = A} ⇒ _⊆_
⊑⇒⊆ []          ()
⊑⇒⊆ (x ∷ xs⊑ys) (here ≡x)    = here ≡x
⊑⇒⊆ (_ ∷ xs⊑ys) (there x∈xs) = there (⊑⇒⊆ (♭ xs⊑ys) x∈xs)

-- The prefix relation forms a poset.

⊑-Poset : ∀ {ℓ} → Set ℓ → Poset _ _ _
⊑-Poset A = record
  { Carrier        = Colist A
  ; _≈_            = _≈_
  ; _≤_            = _⊑_
  ; isPartialOrder = record
    { isPreorder = record
      { isEquivalence = Setoid.isEquivalence (setoid A)
      ; reflexive     = reflexive
      ; trans         = trans
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

  antisym : Antisymmetric _≈_ _⊑_
  antisym []       []        = []
  antisym (x ∷ p₁) (.x ∷ p₂) = x ∷ ♯ antisym (♭ p₁) (♭ p₂)

module ⊑-Reasoning where
  import Relation.Binary.PartialOrderReasoning as POR
  private
    open module R {ℓ} {A : Set ℓ} = POR (⊑-Poset A)
      public renaming (_≤⟨_⟩_ to _⊑⟨_⟩_)

-- The subset relation forms a preorder.

⊆-Preorder : ∀ {ℓ} → Set ℓ → Preorder _ _ _
⊆-Preorder A =
  Ind.InducedPreorder₂ (setoid A) _∈_
                       (λ xs≈ys → ⊑⇒⊆ (⊑P.reflexive xs≈ys))
  where module ⊑P = Poset (⊑-Poset A)

module ⊆-Reasoning where
  import Relation.Binary.PreorderReasoning as PreR
  private
    open module R {ℓ} {A : Set ℓ} = PreR (⊆-Preorder A)
      public renaming (_∼⟨_⟩_ to _⊆⟨_⟩_)

  infix 1 _∈⟨_⟩_

  _∈⟨_⟩_ : ∀ {ℓ} {A : Set ℓ} (x : A) {xs ys} →
           x ∈ xs → xs IsRelatedTo ys → x ∈ ys
  x ∈⟨ x∈xs ⟩ xs⊆ys = (begin xs⊆ys) x∈xs

-- take returns a prefix.

take-⊑ : ∀ {ℓ} {A : Set ℓ} n (xs : Colist A) →
         let toColist = fromList {ℓ} ∘ BVec.toList in
         toColist (take n xs) ⊑ xs
take-⊑ zero    xs       = []
take-⊑ (suc n) []       = []
take-⊑ (suc n) (x ∷ xs) = x ∷ ♯ take-⊑ n (♭ xs)

------------------------------------------------------------------------
-- Finiteness and infiniteness

-- Finite xs means that xs has finite length.

data Finite {ℓ} {A : Set ℓ} : Colist A → Set ℓ where
  []  : Finite []
  _∷_ : ∀ x {xs} (fin : Finite (♭ xs)) → Finite (x ∷ xs)

-- Infinite xs means that xs has infinite length.

data Infinite {ℓ} {A : Set ℓ} : Colist A → Set ℓ where
  _∷_ : ∀ x {xs} (inf : ∞ (Infinite (♭ xs))) → Infinite (x ∷ xs)

-- Colists which are not finite are infinite.

not-finite-is-infinite :
  ∀ {ℓ} {A : Set ℓ} (xs : Colist A) → ¬ Finite xs → Infinite xs
not-finite-is-infinite []       hyp with hyp []
... | ()
not-finite-is-infinite (x ∷ xs) hyp =
  x ∷ ♯ not-finite-is-infinite (♭ xs) (hyp ∘ _∷_ x)

-- Colists are either finite or infinite (classically).

finite-or-infinite :
  -- FIXME <dbrown> Can't make ℓ work here...
  {A : Set} (xs : Colist A) → ¬ ¬ (Finite xs ⊎ Infinite xs)
finite-or-infinite xs = helper <$> excluded-middle
  where
  helper : Dec (Finite xs) → Finite xs ⊎ Infinite xs
  helper (yes fin) = inj₁ fin
  helper (no ¬fin) = inj₂ $ not-finite-is-infinite xs ¬fin

-- Colists are not both finite and infinite.

not-finite-and-infinite :
  ∀ {ℓ} {A : Set ℓ} {xs : Colist A} → Finite xs → Infinite xs → ⊥
not-finite-and-infinite []        ()
not-finite-and-infinite (x ∷ fin) (.x ∷ inf) =
  not-finite-and-infinite fin (♭ inf)
