module _ where -- The top-level module does not count.

module _ where
  private postulate A : Set -- 1.A

module _ where
  private postulate A : Set -- 2.A

module M (_ : Set₁) where -- {mod}M
  module _ where
    private module M₁ where -- {mod}M.3.M₁
    module M₂ where -- {mod}M.M₂
      module _ where
        private postulate A : Set -- M.3.M₂.4.A
    private module M₃ where -- {mod}M.3.M₃
      module _ where
        postulate A : Set -- M.3.M₃.5.A
  module _ where
    module _ where
      module M₃ where -- {mod}M.M₃
        postulate A : Set -- M.M₃.A

B : Set -- B
B = A
  where
  postulate A : Set -- 8.A

C : Set -- C
C = A
  module C where -- {mod}C
  postulate A : Set -- C.A

private module _ where
  postulate A′ : Set -- 9.A′

module _ where
  variable A : Set -- A

module _ where private
  record R : Set₁ where -- 11.R
    constructor c -- N/A
    field
      c : Set -- N/A

private module _ where
  record R : Set₁ where -- 12.R
    constructor c -- N/A
    field
      c : Set -- N/A

    D : Set -- 12.R.D
    D = c

  record R′ : Set where -- 12.R′
    constructor c -- N/A

module _ where private
  data D : Set where -- 13.D
    c : D -- N/A

private module _ where
  data D : Set where -- 14.D
    c : D -- N/A

module _ where
  data D′ : Set where -- D′
    c : D′ -- N/A

-- The following three constructor names (c′, c″ and c‴) are
-- unambiguous, and with some extra work they could perhaps be given
-- unique symbolic anchors, even when --only-scope-checking is used.

pattern c′ = c -- N/A

data D″ : Set where -- D″
  c″ : D″ -- N/A

record R″ : Set where -- R″
  constructor c‴ -- N/A

-- There are symbolic identifiers for module names declared using
-- "import M args as N", but not if "args" is empty.

import Issue4653.M Set as N -- {mod}N
import Agda.Primitive  as N

-- There are no symbolic identifiers for let declarations.

_ : let module O = M; A = Set₁ in A
_ = Set

_ : Set₁
_ = let module O = M Set; A = Set in Set
