module _ where

module A where

  infix 0 c

  data D : Set where
    • : D
    c : D → D → D

  syntax c x y = x + y

module B where

  infix 1 c

  data D : Set where
    • : D
    c : D → D → D

  syntax c x y = x + y

open A
open B

Foo : A.D
Foo = • + •
