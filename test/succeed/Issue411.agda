-- Andreas, 2011-04-26
{-# OPTIONS --universe-polymorphism #-}
module Issue411 where
import Common.Irrelevance  

record A : Set₁ where
  field
    .foo : Set
-- this yielded a panic "-1 not a valid deBruijn index" due to old code for assignS