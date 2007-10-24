{-# OPTIONS -cpp #-}

module TypeChecking.DisplayForm where

import Control.Applicative
import Control.Monad
import Control.Monad.Error

import Syntax.Common
import Syntax.Internal
import TypeChecking.Monad
import TypeChecking.Substitute
import TypeChecking.Reduce
import Syntax.Scope.Base
import Utils.Size

#include "../undefined.h"

displayForm :: QName -> Args -> TCM (Maybe DisplayTerm)
displayForm c vs = do
    odfs  <- defDisplay <$> getConstInfo c
    unless (null odfs) $ verboseS "tc.display.top" 30 $ do
      n <- getContextId
      let fvs = map (\(OpenThing n _) -> n) odfs
      reportSLn "" 0 $ "displayForm: context = " ++ show n ++ ", dfs = " ++ show fvs
    dfs	  <- do
      xs <- mapM tryOpen odfs
      return [ df | Just df <- xs ]
    scope <- getScope
    let matches dfs vs = [ m | Just m <- map (flip matchDisplayForm vs) dfs, inScope scope m ]
    -- Not safe when printing non-terminating terms.
    -- (nfdfs, us) <- normalise (dfs, vs)
    return $ foldr (const . Just) Nothing $ matches dfs vs -- ++ matches nfdfs us
  `catchError` \_ -> return Nothing
  where
    inScope scope d = case hd d of
      Just h  -> maybe False (const True) $ inverseScopeLookupName h scope
      Nothing -> __IMPOSSIBLE__ -- TODO: currently all display forms have heads
    hd (DTerm (Def x _))    = Just x
    hd (DTerm (Con x _))    = Just x
    hd (DWithApp (d : _) _) = hd d
    hd _		    = Nothing

matchDisplayForm :: DisplayForm -> Args -> Maybe DisplayTerm
matchDisplayForm (Display n ps v) vs
  | length ps > length vs = Nothing
  | otherwise             = do
    us <- match n ps $ raise 1 (map unArg vs0)
    return $ substs (reverse us) v `apply` vs1
  where
    (vs0, vs1) = splitAt (length ps) vs

class Match a where
  match :: Nat -> a -> a -> Maybe [Term]

instance Match a => Match [a] where
  match n xs ys = concat <$> zipWithM (match n) xs ys

instance Match a => Match (Arg a) where
  match n p v = match n (unArg p) (unArg v)

instance Match Term where
  match n p v = case (p, v) of
    (Var 0 [], v)                  -> return [subst __IMPOSSIBLE__ v]
    (Var i ps, Var j vs) | i == j  -> match n ps vs
    (Def c ps, Def d vs) | c == d  -> match n ps vs
    (Con c ps, Con d vs) | c == d  -> match n ps vs
    (Lit l, Lit l')      | l == l' -> return []
    (p, v)               | p == v  -> return []
    _                              -> fail ""

