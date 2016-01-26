-- Andreas, 2016-01-13, highlighting of import directives
-- {-# OPTIONS -v highlighting.names:100 -v scope.decl:70 -v tc.decl:10 #-}

module _ where

import Common.Product as Prod hiding (proj₁) -- proj₁ should be highlighted as field

open Prod using (_×_)                        -- _×_ should be highlighted as record type

module M (A : Set) = Prod
  using (_,_)                                -- highlighted as constructor
  renaming (proj₂ to snd)                    -- highlighted as projections
