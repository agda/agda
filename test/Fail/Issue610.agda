-- Andreas, 2012-04-18, bug reported by pumpkingod
module Issue610 where

import Common.Level
open import Common.Equality

data ⊥ : Set where
record ⊤ : Set where

record A : Set₁ where
  constructor set
  field
    .a : Set

.get : A → Set
get x = helper x
  module R where
  helper : .A -> Set
  helper x = A.a x

ack : A → Set
ack x = R.helper x x

hah : set ⊤ ≡ set ⊥
hah = refl

.moo : ⊥
moo with cong ack hah
moo | q = subst (λ x → x) q _

baa : .⊥ → ⊥
baa ()

yoink : ⊥
yoink = baa moo

