module _ where

module A where

  infixl 0 _+_

  data D : Set where
    •   : D
    _+_ : D → D → D

module B where

  infixl 1 _+_

  data D : Set where
    •   : D
    _+_ : D → D → D

module C where

  data D : Set where
    •   : D
    _+_ : D → D → D

open A
open B
open C

Foo : A.D
Foo = • + • + •
