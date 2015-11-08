-- You are not allowed to export the same name twice from a
-- module. However, if the name is only exported once, ambiguity
-- is allowed.
module Issue154 where

module A where
  postulate X : Set

module B where
  postulate X : Set

  module C where
    open A public
    -- X is ambiguous here, but only exported once from C

module D where
  private postulate X : Set
  open A public
  -- same here

module E where
  postulate X : Set
  open A
  -- and here

module F where
  open A public
  open D public
  -- in this case there is no ambiguity, A.X and D.X refer
  -- to the same entity (A.X)

module G where
  open B public

module H where
  open G public
  open B public
  -- same as F but for modules

postulate
  test : A.X → B.X → B.C.X → D.X → E.X → F.X → G.X → H.X
