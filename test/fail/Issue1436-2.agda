module Issue1436-2 where

module A where

  infixl 19 _↑_
  infixl  1 _↓_

  data D : Set where
    ●       : D
    _↓_ _↑_ : D → D → D

module B where

  infix -1000000 _↓_

  data D : Set where
    _↓_ : D → D → D

open A
open B

rejected = ● ↑ ● ↓ ● ↑ ● ↓ ● ↑ ●
