{-# LANGUAGE CPP #-}

module InternalTests.Syntax.Abstract.Name () where

import Agda.Syntax.Abstract.Name
import Agda.Syntax.Fixity

#if __GLASGOW_HASKELL__ <= 708
import Control.Applicative ( (<$>), (<*>) )
#endif

import InternalTests.Syntax.Concrete.Name ()

import Test.QuickCheck

------------------------------------------------------------------------
-- * Arbitrary instances
------------------------------------------------------------------------

-- | The generated names all have the same 'Fixity'': 'noFixity''.

instance Arbitrary Name where
  arbitrary =
    Name <$> arbitrary <*> arbitrary <*> arbitrary
         <*> return noFixity'

instance CoArbitrary Name where
  coarbitrary = coarbitrary . nameId

instance Arbitrary QName where
  arbitrary = do
    ms <- arbitrary
    n  <- arbitrary
    return (QName (MName ms) n)

instance CoArbitrary QName where
  coarbitrary = coarbitrary . qnameName

