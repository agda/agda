module Issue558b where

data Nat : Set where
  Z : Nat
  S : Nat → Nat

data _≡_ {A : Set} (a : A) : A → Set where
  Refl : a ≡ a

plus : Nat → Nat → Nat
plus Z n = n
plus (S n) m = S (plus n m)

data Addable (τ : Set) : Set where
  addable : (τ → τ → τ) → Addable τ

plus' : {τ : Set} → Addable τ → τ → τ → τ
plus' (addable p) = p

record ⊤ : Set where

module AddableM {τ : Set} {a : ⊤} (a : Addable τ) where
  _+_ : τ → τ → τ
  _+_ = plus' a

-- record Addable (τ : Set) : Set where
--  constructor addable
--  field
--   _+_ : τ → τ → τ

open module AddableIFS {t : Set} {a : ⊤} {{r : Addable t}} = AddableM {t} r

data CommAddable (τ : Set) {a : ⊤} : Set where
 commAddable : (addable : Addable τ) → ((a b : τ) → (a + b) ≡ (b + a)) → CommAddable τ

private
  addableCA' : {τ : Set} (ca : CommAddable τ) → Addable τ
  addableCA' (commAddable a _) = a

  comm' : {τ : Set} (ca : CommAddable τ) →
          let a = addableCA' ca in (a b : τ) → (a + b) ≡ (b + a)
  comm' (commAddable _ c) = c

module CommAddableM {τ : Set} {a : ⊤} (ca : CommAddable τ) where
  addableCA : Addable τ
  addableCA = addableCA' ca

  comm : (a b : τ) → (a + b) ≡ (b + a)
  comm = comm' ca

natAdd : Addable Nat
natAdd = addable plus

postulate commPlus : (a b : Nat) → plus a b ≡ plus b a

commNatAdd : CommAddable Nat
commNatAdd = commAddable natAdd commPlus

open CommAddableM {{...}}

test : (Z + Z) ≡ Z
test = comm Z Z

a : {x y : Nat} → (S (S Z) + (x + y)) ≡ ((x + y) + S (S Z))
a {x}{y} = comm (S (S Z)) (x + y)
