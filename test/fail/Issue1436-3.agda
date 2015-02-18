module Issue1436-3 where

module A where

  infix 2 _↑
  infix 1 _↓_

  data D : Set where
    ●   : D
    _↑  : D → D
    _↓_ : D → D → D

module B where

  infix 3 _↓_

  data D : Set where
    _↓_ : D → D → D

open A
open B

-- The expression below is not parsed. If the number 3 above is
-- replaced by 1, then it is parsed…

rejected : A.D
rejected = ● ↑ ↓ ●
