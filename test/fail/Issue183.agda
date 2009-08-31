-- Here is a smaller test case. The error message is produced using
-- the latest (at the time of writing) development version of Agda.

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