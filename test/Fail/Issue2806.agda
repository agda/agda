
data _≡_ {a} {A : Set a} (x : A) : A → Set a where
  refl : x ≡ x

postulate
  A : Set
  a : A

record Eq (a : A) : Set where
  constructor mkEq
  field
    v : A
    p : a ≡ v
open Eq

record S : Set1 where
  constructor mkS
  field
    u : A
    e : Eq u
  open Eq e public
open S

test : ∀ (b : A) → S
u (test b) = b
v (e (test b)) = a
p (e (test b)) = refl
