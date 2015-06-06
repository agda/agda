module _ where

module Test₁ where

  module A where

    infixl 0 _+_

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

module Test₂ where

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
  Foo = • + •

module Test₃ where

  module A where

    data D : Set where
      • : D
      c : D → D → D

    syntax c x y = x + y

  module B where

    data D : Set where
      • : D
      c : D → D → D

    syntax c x y = x + y

  open A
  open B

  Foo : A.D
  Foo = • + •
