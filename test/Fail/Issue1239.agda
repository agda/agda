-- 2014-07-27 Andreas, issue reported by phadei

module _ where

-- trait A { type T <: A }
record A (self : Set) (T : Set) : Set₁ where
  inductive
  field
    T⊂A : T → A T self

-- trait C extends A with B { type T <: C }
record C (self : Set) (T : Set) : Set₁ where
  inductive
  field
    a : A T self
    T⊂C : T → C T self

-- A with B { type T <: A with B { type T <: ... } }
record AB (self : Set) (T : Set) : Set₁ where
  field
    c : C T self

postulate
  Nat Bool : Set

-- Let's give Nat a A∧B trait, with T = Bool
Nat-AB : AB Nat Bool
Nat-AB = {!!}

-- WAS: Non-termination of type-checker (eta-expansion).

-- SHOULD BE: an unsolved meta.
