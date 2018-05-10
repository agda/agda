
module _ where

open import Agda.Builtin.Bool
open import Agda.Builtin.Equality

postulate
  A : Set
  f : .A → A
  g : A → A

mutual
  X : Bool → .A → A
  X = _

  Y : .A → A → A
  Y = _ -- should be solved!

  foo : .(x : A) {y : A} → X true x ≡ g (Y x y)
  foo _ = refl
  -- this prunes both x and y from Y,
  -- so later Y cannot be solved to \ .x y → f x

  bar : .(x : A){y : A} → f x ≡ Y x y
  bar _ = refl
