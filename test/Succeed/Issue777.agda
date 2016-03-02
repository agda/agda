
record R {a} (A : Set a) : Set a where
  field
    some : A

module Works0 where

  works : ∀ {a}{A : Set a} {{r : R A}} -> A
  works = x
    where
      open R {{...}}
      x = some

-- If we add a dummy argument of type Set to "works" we fail, see module Fails
-- below.

-- But there is a chance it still works:

module Works where

  postulate
    works : ∀ {a}{A : Set a} -> A

  test : ∀ {a}{A : Set a} {{r : R A}} -> Set -> A
  test B = x
    where
      open R {{...}}
      x = some

-- Or, we could have an unsolved meta:

module Unsolved where

  postulate
    works : ∀ {a}{A : Set a} {r : R A} -> A

  test : ∀ {a}{A : Set a} {{r : R A}} -> Set -> A
  test B = x
    where
      open R {{...}}
      x = some
  -- unsolved at "x" in "test B = x":
  -- _r_45 : R (R .A)

-- This is the mysterious failure instance:

module Fails where

  fails : ∀ {a}{A : Set a} {{r : R A}} -> Set -> A
  fails B = x
    where
      open R {{...}}
      x = some
  -- No variable of type R (_A_54 .some B) was found in scope
  -- when checking that the expression x has type .A
