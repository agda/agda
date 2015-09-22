module _ where

module A where

  infixl 0 _+_

  data D : Set where
    •   : D
    _+_ : D → D → D

module B where

  infixr 0 _+_

  data D : Set where
    •   : D
    _+_ : D → D → D

open A
open B

Foo : A.D
Foo = • + • + •
