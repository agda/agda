-- Andreas, 2025-09-29, issue #8787:
-- Agda should not print the invisible fields of a record
-- unless --show-implicit is on.
-- This matches the treatment of record constructor applications.

open import Agda.Builtin.Bool
open import Agda.Builtin.Nat
open import Agda.Builtin.Equality

-- A record without constructor, so that Agda prints
-- record patterns and record expressions rather than constructor applications.

record R : Set where
  field
    {n} : Nat
    rf  : n ≡ n

-- A.RecP: case splitting should not produce the hidden field.

f : R → Set
f x = {!x!}  -- C-c C-c x

-- A.RecP: but hidden fields written by the user are preserved by case splitting.

g : R → Bool → Set
g record { n = n ; rf = rf } b = {!b!}  -- C-c C-c b

-- A.Rec: the record expression in the display form of the with-function
-- should not contain the hidden field either.
-- (For expressions, hidden fields are dropped regardless of who wrote them,
-- see test/Fail/ImplicitRecordFields.agda.)

h : R → Nat → Nat
h record { rf = rf } k with k
... | zero  = 0
... | suc l = l

test : (r : R) (k : Nat) → Set
test r k = {! h r k !}  -- C-c C-n
