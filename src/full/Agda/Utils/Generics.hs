{-# OPTIONS -fglasgow-exts #-}

{-| Contains some generic utility functions.
-}
module Agda.Utils.Generics where

import Data.Generics

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
