{-# LANGUAGE Rank2Types #-}
{-| Contains some generic utility functions and reexports certain
    definitions from "Data.Generics".
-}
module Agda.Utils.Generics
  ( module Data.Generics
  , isString
  , everythingBut
  , everywhereBut'
  , everywhereButM'
  ) where

-- The explicit import list is included in order to support several
-- versions of syb; one version of syb contains a definition named
-- everythingBut.
import Data.Generics
  (GenericQ, mkQ, extQ, gmapQ, GenericT, gmapT, GenericM, gmapM)

isString :: GenericQ Bool
isString = mkQ False (const True :: String -> Bool)

everythingBut :: (r -> r -> r) -> GenericQ Bool -> GenericQ r -> GenericQ r
everythingBut (+) stop collect x
    | stop x	= collect x
    | otherwise	= foldr1 (+) $
		    collect x : gmapQ (everythingBut (+) stop collect) x

-- | Same as everywhereBut except that when the stop condition becomes
--   true, the function is called on the top level term (but not on the
--   children).
everywhereBut' :: GenericQ Bool -> GenericT -> GenericT
everywhereBut' q f x
    | q x       = f x
    | otherwise = f (gmapT (everywhereBut' q f) x)

everywhereButM' :: Monad m => GenericQ Bool -> GenericM m -> GenericM m
everywhereButM' q f x
    | q x	= f x
    | otherwise	= f =<< gmapM (everywhereButM' q f) x
