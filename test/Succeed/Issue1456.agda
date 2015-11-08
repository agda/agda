
data Nat : Set where

record Ord (A : Set) : Set where
  field f : A → A

instance
  OrdNat : Ord Nat
  OrdNat = record { f = λ x → x }

postulate
  T : Nat → Set
  R : ∀ {A} {{_ : Ord A}} → A → Set

-- Before solving the type of m, instance search considers it to
-- be a potential candidate for Ord Nat. It then proceeds to check
-- uniqueness by comparing m and OrdNat. The problem was that this
-- left a constraint m == OrdNat that leaked into the state.
foo : Set
foo = ∀ (n : Nat) m → R n → T m
