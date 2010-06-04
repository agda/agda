-- There was a problem with module instantiation if a definition
-- was in scope under more than one name. For instance, constructors
-- or non-private local modules being open publicly. In this case
-- the module instantiation incorrectly generated two separate names
-- for this definition.
module Issue263 where

module M where
  data D : Set where
    d : D
  -- 'M.D.d' is in scope both as 'd' and 'D.d'

  module E where
    postulate X : Set

  open E public
  -- 'M.E.X' is in scope as 'X' and 'E.X'

module M′ = M

bar = M′.E.X  -- this panicked
foo = M′.D.d  -- and this as well
