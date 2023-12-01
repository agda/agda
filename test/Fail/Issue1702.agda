-- Andreas, 2023-09-27, issue #1702
-- Allow private declarations in postulate blocks

postulate
  private
    Foo : Set

module M where

  postulate
    Pub : Set
    private
      Priv : Set

postulate
  pub  : M.Pub
  priv : M.Priv  -- should error
