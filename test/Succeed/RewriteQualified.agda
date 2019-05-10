-- Andreas, 2016-08-01, issue #2125, qualified names in pragmas

{-# OPTIONS --rewriting --confluence-check #-}

import Common.Equality as Eq

{-# BUILTIN REWRITE Eq._≡_ #-} -- qualified name, should be accepted

postulate
  A : Set
  a b : A

module M where
  open Eq
  postulate
    rule : a ≡ b

{-# REWRITE M.rule #-}  -- qualified name, should be accepted

-- ERROR WAS: in the name M.rule, the part M.rule is not valid
-- NOW: works
