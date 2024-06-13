{-# OPTIONS --postfix-projections #-}
module PostfixProjDisplay where  -- issue #7055

open import Agda.Builtin.Equality

postulate
  A : Set
  a : A

record Foo : Set where
  field
    _+_ : A → A → A

record Bar : Set where
  field
    foo : Foo
  open Foo foo public

module M1 (X : Bar) where
  open Bar X

  -- Error message should show a + a
  -- Used to show foo .Foo._+_ a a
  it : a + a ≡ a
  it = refl
