-- Andreas, 2014-09-23
-- Check fixity declarations also in new 'instance' block.

{-# OPTIONS --warning=error #-}

postulate
  D : Set

instance
  infixl 0 D Undeclared
  postulate d : D

-- Should fail with error:
-- Names out of scope in fixity declarations: Undeclared
