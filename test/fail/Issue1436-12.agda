module _ where

module A where

  infix 2 _↑
  infix 1 c

  data D : Set where
    ●  : D
    _↑ : D → D
    c  : {x y : D} → D

  syntax c {x = x} {y = y} = x ↓ y

module B where

  infix 1 c

  data D : Set where
    c : {y x : D} → D

  syntax c {y = y} {x = x} = y ↓ x

open A
open B

rejected : A.D
rejected = ● ↑ ↓ ●
