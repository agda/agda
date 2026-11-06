{-# OPTIONS --sized-types #-}
{-# OPTIONS --guardedness #-}
{-# OPTIONS --no-double-check #-}

-- Andreas, 2026-10-12, issue #8829
-- Recursion justified by a successor-style size pattern .(↑ j)
-- is only sound if the type of the function is upper semi-continuous
-- in the size.
--
-- Each of the following functions terminates only if the size can be
-- used for termination (the data argument is passed through the opaque `pass`),
-- but its type is not admissible.
-- Together, they exercise all the ways the semi-continuity check can fail
-- (see -v term.size.semicont:20).

module Issue8829Inadmissible where

open import Agda.Builtin.Size
open import Agda.Builtin.Bool
open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Agda.Builtin.List
open import Agda.Builtin.Coinduction renaming (∞ to Delay)

data Nat : Size → Set where
  zero : ∀ {i} → Nat (↑ i)
  suc  : ∀ {i} → Nat i → Nat (↑ i)

data Maybe (A : Set) : Set where
  nothing : Maybe A
  just    : A → Maybe A

-- A type given by a field of type Size< i.

data Below (i : Size) : Set where
  below : Size< i → Below i

-- Not a sized type, the size is used as proper index.

data Weird : Size → Set where
  weird : Weird ∞

-- Sized coinductive type (musical coinduction).

data CoNat : Size → Set where
  cozero : ∀ {i} → CoNat (↑ i)
  cosuc  : ∀ {i} → Delay (CoNat i) → CoNat (↑ i)

postulate
  cast  : {A B : Set} → A → B
  idNat : ∀ {i} → Nat i → Nat i
  P     : Size → Set

------------------------------------------------------------------------
-- Argument types that are not lower semi-continuous.

-- Function type whose domain mentions the size.

dom : ∀ {i} → Nat i → (Nat i → Nat i) → Bool
dom zero    f = true
dom (suc n) f = dom (idNat n) (cast f)

-- Function types with infinite domain.

infinite : ∀ {i} → Nat i → (ℕ → Maybe (Nat i)) → Bool
infinite zero    f = true
infinite (suc n) f = infinite (idNat n) (cast f)

maybeInfinite : ∀ {i} → Nat i → (Maybe ℕ → Nat i) → Bool
maybeInfinite zero    f = true
maybeInfinite (suc n) f = maybeInfinite (idNat n) (cast f)

size : ∀ {i} → Nat i → (Size → Nat i) → Bool
size zero    f = true
size (suc n) f = size (idNat n) (cast f)

-- Field of type Size< (↑ i).

bounded : ∀ {i} → Nat i → Below (↑ i) → Bool
bounded zero    x = true
bounded (suc n) x = bounded (idNat n) (cast x)

-- Recursive data type.

list : ∀ {i} → Nat i → List (Nat i) → Bool
list zero    x = true
list (suc n) x = list (idNat n) (cast x)

-- Size in index.

index : ∀ {i} → Nat i → Weird i → Bool
index zero    x = true
index (suc n) x = index (idNat n) (cast x)

-- Coinductive sized type.

conat : ∀ {i} → Nat i → CoNat i → Bool
conat zero    x = true
conat (suc n) x = conat (idNat n) (cast x)

-- Postulated type.

postulated : ∀ {i} → Nat i → P i → Bool
postulated zero    x = true
postulated (suc n) x = postulated (idNat n) (cast x)

-- Type variable.

varType : ∀ {A : Size → Set} {i} → Nat i → A i → Bool
varType {A} zero    x = true
varType {A} (suc n) x = varType {A} (idNat n) (cast x)

------------------------------------------------------------------------
-- Result types that are not upper semi-continuous.

resultIndex : ∀ {i} → Nat i → Weird i
resultIndex zero    = cast true
resultIndex (suc n) = cast (resultIndex (idNat n))

resultVariable : ∀ {A : Size → Set} {i} → Nat i → A i
resultVariable {A} zero    = cast true
resultVariable {A} (suc n) = cast (resultVariable {A} (idNat n))

------------------------------------------------------------------------
-- Copatterns.

record R : Set where
  field
    run : ∀ {i} → Nat i → (ℕ → Maybe (Nat i)) → Bool
open R

r : R
r .run zero    f = true
r .run (suc n) f = r .run (idNat n) (cast f)
