-- Andreas, 2012-04-18, bug reported by sanzhiyan
-- {-# OPTIONS -v tc.with:100 #-}
module Issue610-4 where

import Common.Level
open import Common.Equality

data ⊥ : Set where
record ⊤ : Set where

record A : Set₁ where
  constructor set
  field
    .a : Set

.ack : A → Set
ack x = A.a x

hah : set ⊤ ≡ set ⊥
hah = refl

-- SHOULD FAIL for the same reason that the next decl fails
.moo : ⊥
moo with cong ack hah
moo | q = subst (λ x → x) q _

{- FAILS
.moo' : ⊥
moo' = subst (λ x → x) (cong ack hah) _
-}

baa : .⊥ → ⊥
baa ()

yoink : ⊥
yoink = baa moo

