module _ where

module A where

  infix 2 c
  infix 1 d

  syntax c x   = x ↑
  syntax d x y = x ↓ y

  data D : Set where
    ● : D
    c : D → D
    d : D → D → D

module B where

  syntax d x y = x ↓ y

  data D : Set where
    d : D → D → D

open A
open B

rejected : A.D
rejected = ● ↑ ↓ ●
