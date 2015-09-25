
module Issue493 where

module M where
  postulate A B C : Set

open M using (A) hiding (B)
