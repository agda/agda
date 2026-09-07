-- Andreas, 2014-09-23
-- Check fixity declarations also in new 'instance' block.

postulate
  D : Set

instance
  infixl 0 D Undeclared
  postulate d : D

-- Should fail with error:
-- Names out of scope in fixity declarations: Undeclared

-- warning: -W[no]FixityDeclarationForNonOperator
-- Fixity declarations only apply to proper operators
