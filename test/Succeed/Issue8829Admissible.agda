{-# OPTIONS --sized-types --prop #-}

-- Andreas, 2026-10-12, issue #8829
-- Recursion justified by a successor-style size pattern .(↑ j)
-- is only sound if the type of the function is upper semi-continuous
-- in the size.
--
-- Each of the following functions terminates only because of the size
-- (the data argument is passed through the opaque `pass`),
-- and has an admissible type.
-- Together, they exercise all the rules of the semi-continuity check
-- (see -v term.size.semicont:20).

module Issue8829Admissible where

open import Agda.Builtin.Size
open import Agda.Builtin.Bool
open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Agda.Builtin.Unit
open import Agda.Builtin.Sigma

data Nat : Size → Set where
  zero : ∀ {i} → Nat (↑ i)
  suc  : ∀ {i} → Nat i → Nat (↑ i)

data Maybe (A : Set) : Set where
  nothing : Maybe A
  just    : A → Maybe A

data ⊥ : Set where

-- A type given by a field of type Size< i.

data Below (i : Size) : Set where
  below : Size< i → Below i

-- A finite record type with an irrelevant field.

record Irr : Set where
  field
    .irr : ℕ

-- A proposition.

data Squash (A : Set) : Prop where
  squash : A → Squash A

-- An antitone record type.

record Fun (i : Size) : Set where
  field
    app : Size< i → Bool

-- An antitone coinductive record type.

record Stream (i : Size) : Set where
  coinductive
  field
    head : Bool
    tail : ∀ {j : Size< i} → Stream j

postulate
  cast  : {A B : Set} → A → B
  idNat : ∀ {i} → Nat i → Nat i

------------------------------------------------------------------------
-- Upper semi-continuity of the result type.

-- Size not free in result; LSC: sized inductive type.

notFree : ∀ {i} → Nat i → Bool
notFree zero    = true
notFree (suc n) = notFree (idNat n)

-- Monotone result type.

monotone : ∀ {i} → Nat i → Nat i
monotone zero    = zero
monotone (suc n) = suc (monotone (idNat n))

-- Record type with field of function type in the result.

fun : ∀ {i} → Nat i → Fun i
fun zero    = cast tt
fun (suc n) = cast (fun (idNat n))

-- Coinductive record type in the result.

stream : ∀ {i} → Nat i → Stream i
stream zero    = cast tt
stream (suc n) = cast (stream (idNat n))

------------------------------------------------------------------------
-- Lower semi-continuity of argument types.

-- Antitone argument type.

antitone : ∀ {i} → Nat i → (Nat i → Bool) → Fun i
antitone zero    f = cast tt
antitone (suc n) f = cast (antitone (idNat n) (cast f))

-- Data type with a field Size< i.

belowFun : ∀ {i} → Nat i → Below i → Bool
belowFun zero    x = true
belowFun (suc n) x = belowFun (idNat n) (cast x)

-- Non-recursive data type.

maybe : ∀ {i} → Nat i → Maybe (Nat i) → Bool
maybe zero    x = true
maybe (suc n) x = maybe (idNat n) (cast x)

-- Record type.

sigma : ∀ {i} → Nat i → Σ (Nat i) (λ _ → Bool) → Bool
sigma zero    x = true
sigma (suc n) x = sigma (idNat n) (cast x)

-- Function types with finite domain.

bool : ∀ {i} → Nat i → (Bool → Nat i) → Bool
bool zero    f = true
bool (suc n) f = bool (idNat n) (cast f)

unit : ∀ {i} → Nat i → (⊤ → Nat i) → Bool
unit zero    f = true
unit (suc n) f = unit (idNat n) (cast f)

empty : ∀ {i} → Nat i → (⊥ → Nat i) → Bool
empty zero    f = true
empty (suc n) f = empty (idNat n) (cast f)

maybeBool : ∀ {i} → Nat i → (Maybe (Σ Bool λ _ → Bool) → Nat i) → Bool
maybeBool zero    f = true
maybeBool (suc n) f = maybeBool (idNat n) (cast f)

irrField : ∀ {i} → Nat i → (Irr → Nat i) → Bool
irrField zero    f = true
irrField (suc n) f = irrField (idNat n) (cast f)

irrelevant : ∀ {i} → Nat i → (.ℕ → Nat i) → Bool
irrelevant zero    f = true
irrelevant (suc n) f = irrelevant (idNat n) (cast f)

prop : ∀ {i} → Nat i → (Squash ℕ → Nat i) → Bool
prop zero    f = true
prop (suc n) f = prop (idNat n) (cast f)

------------------------------------------------------------------------
-- Different ways to obtain successor patterns.

-- With-function.

with-fun : ∀ {i} → Nat i → Maybe (Nat i) → Bool
with-fun n x with idNat n
... | zero  = true
... | suc m = with-fun (idNat m) (cast x)

-- Where-function.

where-fun : ∀ {i} → Nat i → Maybe (Nat i) → Bool
where-fun {i} n x = aux (idNat n)
  where
  aux : Nat i → Bool
  aux zero    = true
  aux (suc m) = where-fun (idNat m) (cast x)

-- Copatterns.

record R : Set where
  field
    run : ∀ {i} → Nat i → Maybe (Nat i) → Bool
open R

r : R
r .run zero    x = true
r .run (suc n) x = r .run (idNat n) (cast x)
