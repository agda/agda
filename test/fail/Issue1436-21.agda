module _ where

module A where

  data D : Set where
    •   : D
    _+_ : D → D → D

module B where

  data D : Set where
    •   : D
    _+_ : D → D → D

open A
open B

Foo : A.D
Foo = • + • + •
