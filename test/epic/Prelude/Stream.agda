{-# OPTIONS --universe-polymorphism #-}
module Prelude.Stream where
-- open import Coinduction
  -- Infinite streams.
open import Prelude.IO
open import Prelude.Nat
open import Prelude.Unit

data Level : Set where
  zero : Level
  suc  : (i : Level) → Level

{-# BUILTIN LEVEL     Level #-}
{-# BUILTIN LEVELZERO zero  #-}
{-# BUILTIN LEVELSUC  suc   #-}

infixl 6 _⊔_

_⊔_ : Level → Level → Level
zero  ⊔ j     = j
suc i ⊔ zero  = suc i
suc i ⊔ suc j = suc (i ⊔ j)

{-# BUILTIN LEVELMAX _⊔_ #-}
infix 1000 ♯_

postulate
  ∞  : ∀ {a} (A : Set a) → Set a
  ♯_ : ∀ {a} {A : Set a} → A → ∞ A
  ♭  : ∀ {a} {A : Set a} → ∞ A → A

{-# BUILTIN INFINITY ∞  #-}
{-# BUILTIN SHARP    ♯_ #-}
{-# BUILTIN FLAT     ♭  #-}

data Stream (A : Set) : Set where
  _∷_ : (x : A) (xs : ∞ (Stream A)) → Stream A

-- A stream processor SP A B consumes elements of A and produces
-- elements of B. It can only consume a finite number of A’s before
-- producing a B.

data SP (A B : Set) : Set where
  get : (f : A → SP A B) → SP A B
  put : (b : B) (sp : ∞ (SP A B)) → SP A B

-- The function eat is defined by an outer corecursion into Stream B
-- and an inner recursion on SP A B.

eat : ∀ {A B} → SP A B → Stream A → Stream B
eat (get f)    (a ∷ as) = eat (f a) (♭ as)
eat (put b sp) as       = b ∷ ♯ eat (♭ sp) as

-- Composition of stream processors.

_∘_ : ∀ {A B C} → SP B C → SP A B → SP A C
get f₁    ∘ put x sp₂ = f₁ x ∘ ♭ sp₂
put x sp₁ ∘ sp₂       = put x (♯ (♭ sp₁ ∘ sp₂))
sp₁       ∘ get f₂    = get (λ x → sp₁ ∘ f₂ x)


ones : Stream Nat
ones = 1 ∷ (♯ ones)

twos : Stream Nat
twos = 2 ∷ (♯ twos)


printStream : Nat -> Stream Nat -> IO Unit
printStream Z _ = return unit
printStream (S steps) (n ∷ ns) =
    printNat n ,,
    printStream steps (♭ ns)
    
main : IO Unit
main = printStream 100 twos