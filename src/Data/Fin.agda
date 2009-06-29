------------------------------------------------------------------------
-- Finite sets
------------------------------------------------------------------------

-- Note that elements of Fin n can be seen as natural numbers in the
-- set {m | m < n}. The notation "m" in comments below refers to this
-- natural number view.

module Data.Fin where

open import Data.Nat as Nat
  using (ℕ; zero; suc; z≤n; s≤s)
  renaming ( _+_ to _N+_; _∸_ to _N∸_
           ; _≤_ to _N≤_; _<_ to _N<_; _≤?_ to _N≤?_)
open import Data.Function
open import Relation.Nullary.Decidable
open import Relation.Binary

------------------------------------------------------------------------
-- Types

-- Fin n is a type with n elements.

data Fin : ℕ → Set where
  zero : {n : ℕ} → Fin (suc n)
  suc  : {n : ℕ} (i : Fin n) → Fin (suc n)

-- A conversion: toℕ "n" = n.

toℕ : ∀ {n} → Fin n → ℕ
toℕ zero    = 0
toℕ (suc i) = suc (toℕ i)

-- A Fin-indexed variant of Fin.

Fin′ : ∀ {n} → Fin n → Set
Fin′ i = Fin (toℕ i)

------------------------------------------------------------------------
-- Conversions

-- toℕ is defined above.

-- fromℕ n = "n".

fromℕ : (n : ℕ) → Fin (suc n)
fromℕ zero    = zero
fromℕ (suc n) = suc (fromℕ n)

-- fromℕ≤ {m} _ = "m".

fromℕ≤ : ∀ {m n} → m N< n → Fin n
fromℕ≤ (Nat.s≤s Nat.z≤n)       = zero
fromℕ≤ (Nat.s≤s (Nat.s≤s m≤n)) = suc (fromℕ≤ (Nat.s≤s m≤n))

-- # m = "m".

#_ : ∀ m {n} {m<n : True (suc m N≤? n)} → Fin n
#_ _ {m<n = m<n} = fromℕ≤ (witnessToTruth m<n)

-- raise m "n" = "m + n".

raise : ∀ {m} n → Fin m → Fin (n N+ m)
raise zero    i = i
raise (suc n) i = suc (raise n i)

-- inject⋆ m "n" = "n".

inject : ∀ {n} {i : Fin n} → Fin′ i → Fin n
inject {i = zero}  ()
inject {i = suc i} zero    = zero
inject {i = suc i} (suc j) = suc (inject j)

inject! : ∀ {n} {i : Fin (suc n)} → Fin′ i → Fin n
inject! {n = zero}  {i = suc ()} _
inject!             {i = zero}   ()
inject! {n = suc _} {i = suc _}  zero    = zero
inject! {n = suc _} {i = suc _}  (suc j) = suc (inject! j)

inject+ : ∀ {m} n → Fin m → Fin (m N+ n)
inject+ n zero    = zero
inject+ n (suc i) = suc (inject+ n i)

inject₁ : ∀ {m} → Fin m → Fin (suc m)
inject₁ zero    = zero
inject₁ (suc i) = suc (inject₁ i)

inject≤ : ∀ {m n} → Fin m → m N≤ n → Fin n
inject≤ zero    (Nat.s≤s le) = zero
inject≤ (suc i) (Nat.s≤s le) = suc (inject≤ i le)

------------------------------------------------------------------------
-- Operations

-- Fold.

fold : ∀ (T : ℕ → Set) {m} →
       (∀ {n} → T n → T (suc n)) →
       (∀ {n} → T (suc n)) →
       Fin m → T m
fold T f x zero    = x
fold T f x (suc i) = f (fold T f x i)

-- Lifts functions.

lift : ∀ {m n} k → (Fin m → Fin n) → Fin (k N+ m) → Fin (k N+ n)
lift zero    f i       = f i
lift (suc k) f zero    = zero
lift (suc k) f (suc i) = suc (lift k f i)

-- "m" + "n" = "m + n".

infixl 6 _+_

_+_ : ∀ {m n} (i : Fin m) (j : Fin n) → Fin (toℕ i N+ n)
zero  + j = j
suc i + j = suc (i + j)

-- "m" - "n" = "m ∸ n".

infixl 6 _-_

_-_ : ∀ {m} (i : Fin m) (j : Fin′ (suc i)) → Fin (m N∸ toℕ j)
i     - zero   = i
zero  - suc ()
suc i - suc j  = i - j

-- m ℕ- "n" = "m ∸ n".

infixl 6 _ℕ-_

_ℕ-_ : (n : ℕ) (j : Fin (suc n)) → Fin (suc n N∸ toℕ j)
n     ℕ- zero   = fromℕ n
zero  ℕ- suc ()
suc n ℕ- suc i  = n ℕ- i

-- m ℕ-ℕ "n" = m ∸ n.

infixl 6 _ℕ-ℕ_

_ℕ-ℕ_ : (n : ℕ) → Fin (suc n) → ℕ
n     ℕ-ℕ zero   = n
zero  ℕ-ℕ suc ()
suc n ℕ-ℕ suc i  = n ℕ-ℕ i

-- pred "n" = "pred n".

pred : ∀ {n} → Fin n → Fin n
pred zero    = zero
pred (suc i) = inject₁ i

------------------------------------------------------------------------
-- Order relations

infix 4 _≤_ _<_

_≤_ : ∀ {n} → Rel (Fin n)
_≤_ = _N≤_ on₁ toℕ

_<_ : ∀ {n} → Rel (Fin n)
_<_ = _N<_ on₁ toℕ

data _≺_ : ℕ → ℕ → Set where
  _≻toℕ_ : ∀ n (i : Fin n) → toℕ i ≺ n

-- An ordering view.

data Ordering {n : ℕ} : Fin n → Fin n → Set where
  less    : ∀ greatest (least : Fin′ greatest) →
            Ordering (inject least) greatest
  equal   : ∀ i → Ordering i i
  greater : ∀ greatest (least : Fin′ greatest) →
            Ordering greatest (inject least)

compare : ∀ {n} (i j : Fin n) → Ordering i j
compare zero    zero    = equal   zero
compare zero    (suc j) = less    (suc j) zero
compare (suc i) zero    = greater (suc i) zero
compare (suc i) (suc j) with compare i j
compare (suc .(inject least)) (suc .greatest) | less    greatest least =
                                                  less    (suc greatest) (suc least)
compare (suc .greatest) (suc .(inject least)) | greater greatest least =
                                                  greater (suc greatest) (suc least)
compare (suc .i)        (suc .i)              | equal i = equal (suc i)
