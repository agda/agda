------------------------------------------------------------------------
-- The Agda standard library
--
-- Coinductive vectors
------------------------------------------------------------------------

module Data.Covec where

open import Coinduction
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Conat as Coℕ using (Coℕ; zero; suc; _+_)
open import Data.Cofin using (Cofin; zero; suc)
open import Data.Vec using (Vec; []; _∷_)
open import Data.Colist as Colist using (Colist; []; _∷_)
open import Data.Product using (_,_)
open import Function using (_∋_)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as P using (_≡_)

------------------------------------------------------------------------
-- The type

infixr 5 _∷_
data Covec {a} (A : Set a) : Coℕ → Set a where
  []  : Covec A zero
  _∷_ : ∀ {n} (x : A) (xs : ∞ (Covec A (♭ n))) → Covec A (suc n)

module _ {a} {A : Set a} where

 ∷-injectiveˡ : ∀ {a b} {n} {as bs} → (Covec A (suc n) ∋ a ∷ as) ≡ b ∷ bs → a ≡ b
 ∷-injectiveˡ P.refl = P.refl

 ∷-injectiveʳ : ∀ {a b} {n} {as bs} → (Covec A (suc n) ∋ a ∷ as) ≡ b ∷ bs → as ≡ bs
 ∷-injectiveʳ P.refl = P.refl

------------------------------------------------------------------------
-- Some operations

map : ∀ {a b} {A : Set a} {B : Set b} {n} → (A → B) → Covec A n → Covec B n
map f []       = []
map f (x ∷ xs) = f x ∷ ♯ map f (♭ xs)

module _ {a} {A : Set a} where

 fromVec : ∀ {n} → Vec A n → Covec A (Coℕ.fromℕ n)
 fromVec []       = []
 fromVec (x ∷ xs) = x ∷ ♯ fromVec xs

 fromColist : (xs : Colist A) → Covec A (Colist.length xs)
 fromColist []       = []
 fromColist (x ∷ xs) = x ∷ ♯ fromColist (♭ xs)

 take : ∀ m {n} → Covec A (m + n) → Covec A m
 take zero    xs       = []
 take (suc n) (x ∷ xs) = x ∷ ♯ take (♭ n) (♭ xs)

 drop : ∀ m {n} → Covec A (Coℕ.fromℕ m + n) → Covec A n
 drop zero    xs       = xs
 drop (suc n) (x ∷ xs) = drop n (♭ xs)

 replicate : ∀ n → A → Covec A n
 replicate zero    x = []
 replicate (suc n) x = x ∷ ♯ replicate (♭ n) x

 lookup : ∀ {n} → Cofin n → Covec A n → A
 lookup zero    (x ∷ xs) = x
 lookup (suc n) (x ∷ xs) = lookup n (♭ xs)

 infixr 5 _++_

 _++_ : ∀ {m n} → Covec A m → Covec A n → Covec A (m + n)
 []       ++ ys = ys
 (x ∷ xs) ++ ys = x ∷ ♯ (♭ xs ++ ys)

 [_] : A → Covec A (suc (♯ zero))
 [ x ] = x ∷ ♯ []

------------------------------------------------------------------------
-- Equality and other relations

-- xs ≈ ys means that xs and ys are equal.

 infix 4 _≈_

 data _≈_ : ∀ {n} (xs ys : Covec A n) → Set where
   []  : [] ≈ []
   _∷_ : ∀ {n} x {xs ys}
         (xs≈ : ∞ (♭ xs ≈ ♭ ys)) → _≈_ {n = suc n} (x ∷ xs) (x ∷ ys)

-- x ∈ xs means that x is a member of xs.

 infix 4 _∈_

 data _∈_ : ∀ {n} → A → Covec A n → Set where
   here  : ∀ {n x  } {xs}                   → _∈_ {n = suc n} x (x ∷ xs)
   there : ∀ {n x y} {xs} (x∈xs : x ∈ ♭ xs) → _∈_ {n = suc n} x (y ∷ xs)

-- xs ⊑ ys means that xs is a prefix of ys.

 infix 4 _⊑_

 data _⊑_ : ∀ {m n} → Covec A m → Covec A n → Set where
   []  : ∀ {n} {ys : Covec A n} → [] ⊑ ys
   _∷_ : ∀ {m n} x {xs ys} (p : ∞ (♭ xs ⊑ ♭ ys)) →
         _⊑_ {m = suc m} {suc n} (x ∷ xs) (x ∷ ys)

------------------------------------------------------------------------
-- Some proofs

setoid : ∀ {a} → Set a → Coℕ → Setoid _ _
setoid A n = record
  { Carrier       = Covec A n
  ; _≈_           = _≈_
  ; isEquivalence = record
    { refl  = refl
    ; sym   = sym
    ; trans = trans
    }
  }
  where
  refl : ∀ {n} → Reflexive (_≈_ {n = n})
  refl {x = []}     = []
  refl {x = x ∷ xs} = x ∷ ♯ refl

  sym : ∀ {n} → Symmetric (_≈_ {A = A} {n})
  sym []        = []
  sym (x ∷ xs≈) = x ∷ ♯ sym (♭ xs≈)

  trans : ∀ {n} → Transitive (_≈_ {A = A} {n})
  trans []        []         = []
  trans (x ∷ xs≈) (.x ∷ ys≈) = x ∷ ♯ trans (♭ xs≈) (♭ ys≈)

poset : ∀ {a} → Set a → Coℕ → Poset _ _ _
poset A n = record
  { Carrier        = Covec A n
  ; _≈_            = _≈_
  ; _≤_            = _⊑_
  ; isPartialOrder = record
    { isPreorder = record
      { isEquivalence = Setoid.isEquivalence (setoid A n)
      ; reflexive     = reflexive
      ; trans         = trans
      }
    ; antisym  = antisym
    }
  }
  where
  reflexive : ∀ {n} → _≈_ {n = n} ⇒ _⊑_
  reflexive []        = []
  reflexive (x ∷ xs≈) = x ∷ ♯ reflexive (♭ xs≈)

  trans : ∀ {n} → Transitive (_⊑_ {n = n})
  trans []        _          = []
  trans (x ∷ xs≈) (.x ∷ ys≈) = x ∷ ♯ trans (♭ xs≈) (♭ ys≈)

  antisym : ∀ {n} → Antisymmetric (_≈_ {n = n}) _⊑_
  antisym []       []        = []
  antisym (x ∷ p₁) (.x ∷ p₂) = x ∷ ♯ antisym (♭ p₁) (♭ p₂)

map-cong : ∀ {a b} {A : Set a} {B : Set b} {n} (f : A → B) → _≈_ {n = n} =[ map f ]⇒ _≈_
map-cong f []        = []
map-cong f (x ∷ xs≈) = f x ∷ ♯ map-cong f (♭ xs≈)

take-⊑ : ∀ {a} {A : Set a} m {n} (xs : Covec A (m + n)) → take m xs ⊑ xs
take-⊑ zero    xs       = []
take-⊑ (suc n) (x ∷ xs) = x ∷ ♯ take-⊑ (♭ n) (♭ xs)
