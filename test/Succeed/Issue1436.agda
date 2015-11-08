module Issue1436 where

module A where

  infix 2 _↑
  infix 1 _↓_

  data D : Set where
    ●   : D
    _↑  : D → D
    _↓_ : D → D → D

module B where

  infix 1 _↓_

  data D : Set where
    _↓_ : D → D → D

open A
open B

rejected : A.D
rejected = ● ↑ ↓ ●
