
module Issue183 where

postulate A : Set

T : Set
T = A → A

data L (A : Set) : Set where

data E (x : T) : T → Set where
  e : E x x

foo : (f : A → A) → L (E f (λ x → f x))
foo = λ _ → e

-- Previously:
-- An internal error has occurred. Please report this as a bug.
-- Location of the error: src/full/Agda/Syntax/Translation/AbstractToConcrete.hs:705
-- Should now give a proper error message.

-- E (_8 f) (_8 f) !=< L (E f f) of type Set
-- when checking that the expression e has type L (E f f)
