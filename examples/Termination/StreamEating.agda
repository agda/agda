{-
Stream transducers have been described in:

  N. Ghani, P. Hancock, and D. Pattinson,
  Continuous functions on final coalgebras.
  In Proc. CMCS 2006, Electr. Notes in Theoret. Comp. Sci., 2006.

They have been modelled by mixed equi-(co)inductive sized types in

  A. Abel,
  Mixed Inductive/Coinductive Types and Strong Normalization.
  In APLAS 2007, LNCS 4807.

Here we model them by mutual data/codata and mixed recursion/corecursion.
Cf. examples/Termination/StreamProc.agda
 -}

module StreamEating where

open import Common.Coinduction

-- Infinite streams.

data Stream (A : Set) : Set where
  _∷_ : (x : A) (xs : ∞ (Stream A)) → Stream A

-- A stream processor SP A B consumes elements of A and produces
-- elements of B. It can only consume a finite number of A's before
-- producing a B.

data SP (A B : Set) : Set where
  get : (f : A → SP A B) → SP A B
  put : (b : B) (sp : ∞ (SP A B)) → SP A B

-- eat is defined by (outer) corecursion into Stream B
-- and an inner recursion on SP A B
eat : ∀ {A B} → SP A B → Stream A → Stream B
eat (get f)    (a ∷ as) = eat (f a) (♭ as)
eat (put b sp) as       = b ∷ ♯ eat (♭ sp) as

_∘_ : ∀ {A B C} → SP B C → SP A B → SP A C
get f₁    ∘ put x sp₂ = f₁ x ∘ ♭ sp₂
put x sp₁ ∘ sp₂       = put x (♯ (♭ sp₁ ∘ sp₂))
sp₁       ∘ get f₂    = get (λ x → sp₁ ∘ f₂ x)
