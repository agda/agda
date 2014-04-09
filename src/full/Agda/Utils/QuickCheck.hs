{-# LANGUAGE CPP #-}
module Agda.Utils.QuickCheck
  ( module Test.QuickCheck
  , module Agda.Utils.QuickCheck
  ) where

#if MIN_VERSION_QuickCheck(2,7,0)
import Test.QuickCheck hiding ((===))
import Test.QuickCheck.Property (Property(..))
#else
import Test.QuickCheck hiding (ranges)
#endif

isSuccess :: Result -> Bool
isSuccess Success{} = True
isSuccess _         = False

quickCheck' :: Testable prop => prop -> IO Bool
quickCheck' p = fmap isSuccess $ quickCheckResult p

quickCheckWith' :: Testable prop => Args -> prop -> IO Bool
quickCheckWith' args p = fmap isSuccess $ quickCheckWithResult args p

divPropSize :: Int -> Property -> Property
#if MIN_VERSION_QuickCheck(2,7,0)
divPropSize k (MkProperty prop) =
  MkProperty $ sized $ \n -> resize (n `div` k) prop
#else
divPropSize k prop = sized $ \n -> resize (n `div` k) prop
#endif

