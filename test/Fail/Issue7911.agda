
module _ where

postulate
  I : Set

  instance i : I

  D : I → Set
  Foo : ∀ {j} → D j → Set
  foo : ⦃ j : I ⦄ (d : D j) → Foo d

bar : ⦃ j : I ⦄ (d : D j) → Foo d
bar d = foo d
