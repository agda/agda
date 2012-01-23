module Issue558 where

data Nat : Set where
  Z : Nat
  S : Nat → Nat

data _≡_ {A : Set} (a : A) : A → Set where
  Refl : a ≡ a

plus : Nat → Nat → Nat
plus Z n = n
plus (S n) m = S (plus n m)

record Addable (τ : Set) : Set where
 constructor addable
 field
  _+_ : τ → τ → τ

open module AddableIFS {t : Set} {{r : Addable t}} = Addable {t} r

record CommAddable (τ : Set) : Set where
 constructor commAddable
 field
  foo : Addable τ
  comm : (a b : τ) → (a + b) ≡ (b + a)

natAdd : Addable Nat
natAdd = record {_+_ = plus}

postulate commPlus : (a b : Nat) → plus a b ≡ plus b a

commAdd : CommAddable Nat
commAdd = record {foo = natAdd; comm = commPlus}

open CommAddable {{...}}

test : (Z + Z) ≡ Z
test = comm Z Z

a : {x y : Nat} → (S (S Z) + (x + y)) ≡ ((x + y) + S (S Z))
a {x}{y} = comm (S (S Z)) (x + y) -- ERROR!
