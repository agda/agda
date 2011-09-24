------------------------------------------------------------------------
-- The Agda standard library
--
-- Coinductive lists
------------------------------------------------------------------------

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
open import Level using (_⊔_)
open import Relation.Binary
import Relation.Binary.InducedPreorders as Ind
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary
open import Relation.Nullary.Negation
open RawMonad (¬¬-Monad {p = Level.zero})

------------------------------------------------------------------------
-- The type

infixr 5 _∷_

data Colist {a} (A : Set a) : Set a where
  []  : Colist A
  _∷_ : (x : A) (xs : ∞ (Colist A)) → Colist A

{-# IMPORT Data.FFI #-}
{-# COMPILED_DATA Colist Data.FFI.AgdaList [] (:) #-}

data Any {a p} {A : Set a} (P : A → Set p) :
         Colist A → Set (a ⊔ p) where
  here  : ∀ {x xs} (px  : P x)          → Any P (x ∷ xs)
  there : ∀ {x xs} (pxs : Any P (♭ xs)) → Any P (x ∷ xs)

data All {a p} {A : Set a} (P : A → Set p) :
         Colist A → Set (a ⊔ p) where
  []  : All P []
  _∷_ : ∀ {x xs} (px : P x) (pxs : ∞ (All P (♭ xs))) → All P (x ∷ xs)

------------------------------------------------------------------------
-- Some operations

null : ∀ {a} {A : Set a} → Colist A → Bool
null []      = true
null (_ ∷ _) = false

length : ∀ {a} {A : Set a} → Colist A → Coℕ
length []       = zero
length (x ∷ xs) = suc (♯ length (♭ xs))

map : ∀ {a b} {A : Set a} {B : Set b} → (A → B) → Colist A → Colist B
map f []       = []
map f (x ∷ xs) = f x ∷ ♯ map f (♭ xs)

fromList : ∀ {a} {A : Set a} → List A → Colist A
fromList []       = []
fromList (x ∷ xs) = x ∷ ♯ fromList xs

take : ∀ {a} {A : Set a} (n : ℕ) → Colist A → BoundedVec A n
take zero    xs       = []
take (suc n) []       = []
take (suc n) (x ∷ xs) = x ∷ take n (♭ xs)

replicate : ∀ {a} {A : Set a} → Coℕ → A → Colist A
replicate zero    x = []
replicate (suc n) x = x ∷ ♯ replicate (♭ n) x

lookup : ∀ {a} {A : Set a} → ℕ → Colist A → Maybe A
lookup n       []       = nothing
lookup zero    (x ∷ xs) = just x
lookup (suc n) (x ∷ xs) = lookup n (♭ xs)

infixr 5 _++_

_++_ : ∀ {a} {A : Set a} → Colist A → Colist A → Colist A
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ ♯ (♭ xs ++ ys)

concat : ∀ {a} {A : Set a} → Colist (List⁺ A) → Colist A
concat []               = []
concat ([ x ]⁺   ∷ xss) = x ∷ ♯ concat (♭ xss)
concat ((x ∷ xs) ∷ xss) = x ∷ ♯ concat (xs ∷ xss)

[_] : ∀ {a} {A : Set a} → A → Colist A
[ x ] = x ∷ ♯ []

------------------------------------------------------------------------
-- Equality

-- xs ≈ ys means that xs and ys are equal.

infix 4 _≈_

data _≈_ {a} {A : Set a} : (xs ys : Colist A) → Set a where
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
    open module R {a} {A : Set a} = EqR (setoid A) public

-- map preserves equality.

map-cong : ∀ {a b} {A : Set a} {B : Set b}
           (f : A → B) → _≈_ =[ map f ]⇒ _≈_
map-cong f []        = []
map-cong f (x ∷ xs≈) = f x ∷ ♯ map-cong f (♭ xs≈)

------------------------------------------------------------------------
-- Memberships, subsets, prefixes

-- x ∈ xs means that x is a member of xs.

infix 4 _∈_

_∈_ : ∀ {a} → {A : Set a} → A → Colist A → Set a
x ∈ xs = Any (_≡_ x) xs

-- xs ⊆ ys means that xs is a subset of ys.

infix 4 _⊆_

_⊆_ : ∀ {a} → {A : Set a} → Colist A → Colist A → Set a
xs ⊆ ys = ∀ {x} → x ∈ xs → x ∈ ys

-- xs ⊑ ys means that xs is a prefix of ys.

infix 4 _⊑_

data _⊑_ {a} {A : Set a} : Colist A → Colist A → Set a where
  []  : ∀ {ys}                            → []     ⊑ ys
  _∷_ : ∀ x {xs ys} (p : ∞ (♭ xs ⊑ ♭ ys)) → x ∷ xs ⊑ x ∷ ys

-- Prefixes are subsets.

⊑⇒⊆ : ∀ {a} → {A : Set a} → _⊑_ {A = A} ⇒ _⊆_
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
    open module R {a} {A : Set a} = POR (⊑-Poset A)
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
    open module R {a} {A : Set a} = PreR (⊆-Preorder A)
      public renaming (_∼⟨_⟩_ to _⊆⟨_⟩_)

  infix 1 _∈⟨_⟩_

  _∈⟨_⟩_ : ∀ {a} {A : Set a} (x : A) {xs ys} →
           x ∈ xs → xs IsRelatedTo ys → x ∈ ys
  x ∈⟨ x∈xs ⟩ xs⊆ys = (begin xs⊆ys) x∈xs

-- take returns a prefix.

take-⊑ : ∀ {a} {A : Set a} n (xs : Colist A) →
         let toColist = fromList {a} ∘ BVec.toList in
         toColist (take n xs) ⊑ xs
take-⊑ zero    xs       = []
take-⊑ (suc n) []       = []
take-⊑ (suc n) (x ∷ xs) = x ∷ ♯ take-⊑ n (♭ xs)

------------------------------------------------------------------------
-- Finiteness and infiniteness

-- Finite xs means that xs has finite length.

data Finite {a} {A : Set a} : Colist A → Set a where
  []  : Finite []
  _∷_ : ∀ x {xs} (fin : Finite (♭ xs)) → Finite (x ∷ xs)

-- Infinite xs means that xs has infinite length.

data Infinite {a} {A : Set a} : Colist A → Set a where
  _∷_ : ∀ x {xs} (inf : ∞ (Infinite (♭ xs))) → Infinite (x ∷ xs)

-- Colists which are not finite are infinite.

not-finite-is-infinite :
  ∀ {a} {A : Set a} (xs : Colist A) → ¬ Finite xs → Infinite xs
not-finite-is-infinite []       hyp with hyp []
... | ()
not-finite-is-infinite (x ∷ xs) hyp =
  x ∷ ♯ not-finite-is-infinite (♭ xs) (hyp ∘ _∷_ x)

-- Colists are either finite or infinite (classically).
--
-- TODO: Make this definition universe polymorphic.

finite-or-infinite :
  {A : Set} (xs : Colist A) → ¬ ¬ (Finite xs ⊎ Infinite xs)
finite-or-infinite xs = helper <$> excluded-middle
  where
  helper : Dec (Finite xs) → Finite xs ⊎ Infinite xs
  helper (yes fin) = inj₁ fin
  helper (no ¬fin) = inj₂ $ not-finite-is-infinite xs ¬fin

-- Colists are not both finite and infinite.

not-finite-and-infinite :
  ∀ {a} {A : Set a} {xs : Colist A} → Finite xs → Infinite xs → ⊥
not-finite-and-infinite []        ()
not-finite-and-infinite (x ∷ fin) (.x ∷ inf) =
  not-finite-and-infinite fin (♭ inf)
