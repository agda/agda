-- Andreas, 2016-06-13 issue #2027: Unbound variables in pattern synonyms
-- Quiz by Ulf

postulate Nat : Set

pattern hm = x
-- This pattern synonym should fail with a message like
-- Unbound variables in pattern synonym:  x

quiz₁ : Nat → Nat → Nat
quiz₁ hm hm = hm

quiz₂ : Nat → Nat
quiz₂ x = hm

quiz₃ : Nat → Nat
quiz₃ hm = x
-- OLD ERROR: Not in scope: x
