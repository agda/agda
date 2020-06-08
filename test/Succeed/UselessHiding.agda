-- Was: test/Fail/Issue493
-- Andreas, 2020-06-08, issue #4737
-- Warn instead of hard error on useless hiding.

module _ where

module M where
  postulate A B C : Set
  data D : Set where

open M using (A) hiding (B; module D)
