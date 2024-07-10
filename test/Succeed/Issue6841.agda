open import Agda.Builtin.Equality

postulate A : Set; a : A

data MaybeA : Set where
  just : A → MaybeA
  nothing : MaybeA

withIn-bug : A
withIn-bug with just a in eq
... | just y = y
