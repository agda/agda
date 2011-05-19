-- {-# OPTIONS -v tc.rec:100 -v tc.signature:20 #-}

module Issue414 where

record P : Set₁ where 
  field
    q : Set

  x : P
  x = record { q = q }
-- Andreas 2011-05-19
-- record constructor should have been added to the signature
-- before record module is constructed!