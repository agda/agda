-- ASR (29 September 2014). Adapted from the reported example in
-- issue 1269.

open import Common.Product
open import Common.Reflection
open import Common.Equality

postulate
  A : Set
  P : A → Set

postulate foo : ∃ P

fooTerm : Term
fooTerm with primQNameType (quote foo)
... | el s t = t

fooTerm' : Term
fooTerm' = quoteTerm (∃ P)

ok : fooTerm ≡ fooTerm'
ok = refl
