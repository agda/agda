-- Andreas, 2016-11-19 issue #2309
-- No-eta-equality needs to be respected in pattern matching
-- also before the clause compiler.

record Unit : Set where
  pattern; constructor unit
  no-eta-equality

record R : Set₁ where
  field Fst : Unit → Set
        Snd : (x : Unit) → Fst x
open R

Test : (A : Set) (a : A) → R
Fst (Test A a) unit = A
Snd (Test A a) x    = a  -- should not be accepted
