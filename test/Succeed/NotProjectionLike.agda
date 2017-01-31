-- Andreas, 2017-01-26

-- A hopefully exhaustive list of reasons why a function cannot
-- be projection-like.  The correctness is ensured by triggering
-- a crash if any of the functions in this file is projection-like.

{-# OPTIONS -v tc.proj.like.crash:1000 #-}

data ⊥ : Set where
record ⊤ : Set where

data Bool : Set where
  true false : Bool

open import Common.List


-- Not projection-like because recursive.
-- (Could be changed).

id' : ∀{A : Set} (xs : List A) → List A
id' [] = []
id' (x ∷ xs) = x ∷ id' xs

-- Not projection-like because constructor-headed.
-- (Could this be changed?)

NonEmpty : ∀{A : Set} (xs : List A) → Set
NonEmpty []       = ⊥
NonEmpty (x ∷ xs) = ⊤

-- Not projection-like because of absurd match.
-- Reason: we cannot infer the value of @A@ for stuck @head [] p@.

head : ∀{A : Set} (xs : List A) (p : NonEmpty xs) → A
head []       ()
head (x ∷ xs) _ = x

-- Not projection-like because of matching on non-principal argument.
-- Reason: we cannot infer the value of @A@ for @dropHeadIf (x ∷ xs) b@.
-- (Constructor applications are not inferable in general.)

dropHeadIf : ∀{A : Set} (xs : List A) (b : Bool) → List A
dropHeadIf (_ ∷ xs) true = xs
dropHeadIf xs _ = xs

-- Not projection-like because of deep matching.
-- Reason: we cannot infer @A@ for @drop2 (x ∷ xs)@.

drop2 : ∀{A : Set} (xs : List A) → List A
drop2 (_ ∷ (_ ∷ xs)) = xs
drop2 xs = xs

-- Not projection-like because @abstract@.
-- Reason: @tail []@ is stuck outside of the abstract block.

abstract
  tail : ∀{A : Set} (xs : List A) → List A
  tail [] = []
  tail (_ ∷ xs) = xs

-- Not projection-like because mutually defined.

mutual
  odds : ∀{A : Set} (xs : List A) → List A
  odds []       = []
  odds (x ∷ xs) = evens xs

  postulate
    evens : ∀{A : Set} (xs : List A) → List A
    -- evens [] = []
    -- evens (x ∷ xs) = x ∷ odds xs

-- Not projection-like because no parameters.

IsTrue : Bool → Set
IsTrue true  = ⊤
IsTrue false = ⊥

-- Not projection-like because type can reduce.

idTrue : (b : Bool) (p : IsTrue b) → Bool
idTrue b p = b

-- Not projection-like because it returns a paramter

par : {A : Set} (xs : List A) → Set
par {A} xs = A
