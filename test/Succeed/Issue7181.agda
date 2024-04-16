open import Agda.Builtin.Sigma
open import Agda.Builtin.Nat

-- Copatterns

data D : Nat → Set where
  c1 : (x : Nat) → D (suc x)
  c2 : (x : Nat) → D x

f : (x : Nat) → D x → Σ Set (λ A → A)

fst (f .(suc x) (c1 x)) = Nat
snd (f .(suc x) (c1 x)) = zero

fst (f .x (c2 x)) = Nat
snd (f .x (c2 x)) = zero

g : (x : Nat) → fst (f x (c2 x))
g x = zero

-- Indexed induction-recursion

postulate P : Nat → Set

data U : Nat → Set
El : (x : Nat) → U x → Set

data U where
  c1 : (x : Nat) → U (suc x)
  c2 : (x : Nat) → U x
  c3 : (x : Nat) → El x (c2 x) → U x

El .(suc x) (c1 x)   = Nat
El .x       (c2 x)   = Nat
El .x       (c3 x y) = P y

-- Induction-induction

data D1 : Nat → Set
data D2 : (x : Nat) → D1 x → Set

data D1 where
  c1 : (x : Nat) → D1 (suc x)
  c2 : (x : Nat) → D1 x
  c3 : (x : Nat) → D2 x (c2 x) → D1 x

data D2 where
  c4 : (x : Nat) → D2 x (c2 x)

module _
  (P1 : Nat → Set)
  (P2 : (x : Nat) → P1 x → Set)
  (p1 : (x : Nat) → P1 (suc x))
  (p2 : (x : Nat) → P1 x)
  (p3 : (x : Nat) → P2 x (p2 x) → P1 x)
  (p4 : (x : Nat) → P2 x (p2 x))
  where

  rec1 : (x : Nat) → D1 x → P1 x
  rec2 : (x : Nat) (d1 : D1 x) → D2 x d1 → P2 x (rec1 x d1)

  rec1 .(suc x) (c1 x)    = p1 x
  rec1 .x       (c2 x)    = p2 x
  rec1 .x       (c3 x d2) = p3 x (rec2 x (c2 x) d2)

  rec2 .x .(c2 x) (c4 x) = p4 x
