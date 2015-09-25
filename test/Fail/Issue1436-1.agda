module Issue1436-1 where

module A where

  infixl 20 _↑_
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

-- The expression below is not parsed. If the number 20 above is
-- replaced by 19, then it is parsed…

rejected = ● ↑ ● ↓ ● ↑ ● ↓ ● ↑ ●
