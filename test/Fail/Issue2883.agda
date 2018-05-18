
open import Agda.Builtin.Nat
open import Agda.Builtin.Sigma
open import Agda.Builtin.Equality

data I : Set where
  it : I

data D : I → Set where
  d : D it

data Box : Set where
  [_] : Nat → Box

mutual
  data Code : Set where
    d   : I → Code
    box : Code
    sg  : (a : Code) → (El a → Code) → Code

  El : Code → Set
  El (d i)    = D i
  El box      = Box
  El (sg a f) = Σ (El a) λ x → El (f x)

foo : (i : I) → Code
foo i = sg (d i) aux
  where
    aux : D i → Code
    aux d = sg box λ { [ a ] → box }

crash : ∀ i → El (foo i) → Nat
crash i (d , p) = p
