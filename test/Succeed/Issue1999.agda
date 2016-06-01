-- Andreas, 2016-06-01, issue 1999

-- Bug in TypeChecking.Signature.applySection
-- If that function was not such horrible spaghetti code,
-- there would be less bugs like this.
-- Bug was: code for applying projection used ts instead of ts'

-- {-# OPTIONS -v tc.mod.apply:80 #-}

module Issue1999 where

import Common.Product as P using (_×_ ; proj₂)

module One (A : Set) where
  open P public

module Two (A : Set) where
  module M = One A

  myproj : A M.× A → A
  myproj p = M.proj₂ p

-- WAS: Internal error in Substitute (projection applied to lambda)
-- Should work.
