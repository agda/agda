{-# LANGUAGE CPP, FlexibleInstances, TypeSynonymInstances #-}

module Agda.TypeChecking.DisplayForm where

import Control.Applicative
import Control.Monad.Error
import Control.Monad.Trans.Maybe

import Data.Traversable (traverse)

import Agda.Syntax.Common hiding (Arg, Dom, NamedArg, ArgInfo)
import Agda.Syntax.Internal
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Level

#include "../undefined.h"
import Agda.Utils.Impossible

displayForm :: QName -> Args -> TCM (Maybe DisplayTerm)
displayForm c vs = do
    odfs  <- defDisplay <$> getConstInfo c
    unless (null odfs) $ verboseS "tc.display.top" 100 $ do
      n <- getContextId
      let fvs = map (\(OpenThing n _) -> n) odfs
      reportSLn "tc.display.top" 100 $ "displayForm: context = " ++ show n ++ ", dfs = " ++ show fvs
    dfs	  <- do
      xs <- mapM tryOpen odfs
      return [ df | Just df <- xs ]
    scope <- getScope
    ms <- do
      ms <- mapM (runMaybeT . (`matchDisplayForm` vs)) dfs
      return [ m | Just m <- ms, inScope scope m ]
    -- Not safe when printing non-terminating terms.
    -- (nfdfs, us) <- normalise (dfs, vs)
    unless (null odfs) $ reportSLn "tc.display.top" 100 $ unlines
      [ "name        : " ++ show c
      , "displayForms: " ++ show dfs
      , "arguments   : " ++ show vs
      , "matches     : " ++ show ms
      , "result      : " ++ show (foldr (const . Just) Nothing ms)
      ]
    return $ foldr (const . Just) Nothing ms
  `catchError` \_ -> return Nothing
  where
    inScope _ _ = True  -- TODO: distinguish between with display forms and other display forms
--     inScope scope d = case hd d of
--       Just h  -> maybe False (const True) $ inverseScopeLookupName h scope
--       Nothing -> __IMPOSSIBLE__ -- TODO: currently all display forms have heads
    hd (DTerm (Def x _))    = Just x
    hd (DTerm (Con x _))    = Just $ conName x
    hd (DTerm (Shared p))   = hd (DTerm $ derefPtr p)
    hd (DWithApp (d : _) _) = hd d
    hd _		    = Nothing

-- | Match a 'DisplayForm' @n |- q ps = v@ against @q vs@.
--   Return the 'DisplayTerm' @v[us]@ if the match was successful,
--   i.e., @vs / ps = Just us@
matchDisplayForm :: DisplayForm -> Args -> MaybeT TCM DisplayTerm
matchDisplayForm (Display n ps v) vs
  | length ps > length vs = mzero
  | otherwise             = do
      us <- match n ps $ raise 1 $ map unArg vs0
      return $ applySubst (parallelS $ reverse us) v `apply` vs1
  where
    (vs0, vs1) = splitAt (length ps) vs

class Match a where
  match :: Nat -> a -> a -> MaybeT TCM [Term]

instance Match a => Match [a] where
  match n xs ys = concat <$> zipWithM (match n) xs ys

instance Match a => Match (Arg a) where
  match n p v = match n (unArg p) (unArg v)

instance Match a => Match (Elim' a) where
  match n p v =
    case (p, v) of
      (Proj f, Proj f') | f == f' -> return []
      (Apply a, Apply a')         -> match n a a'
      _                           -> mzero

instance Match Term where
  match n p v = case (ignoreSharing p, ignoreSharing v) of
    (Var 0 [], v)                  -> return [subst __IMPOSSIBLE__ v]
    (Var i ps, Var j vs) | i == j  -> match n ps vs
    (Def c ps, Def d vs) | c == d  -> match n ps vs
    (Con c ps, Con d vs) | c == d  -> match n ps vs
    (Lit l, Lit l')      | l == l' -> return []
    (p, v)               | p == v  -> return []
    (p, Level l)                   -> match n p =<< reallyUnLevelView l
    (Sort ps, Sort pv)             -> match n ps pv
    (p, Sort (Type v))             -> match n p =<< reallyUnLevelView v
    _                              -> mzero

instance Match Sort where
  match n p v = case (p, v) of
    (Type pl, Type vl) -> match n pl vl
    _ | p == v -> return []
    _          -> mzero

instance Match Level where
  match n p v = do
    p <- reallyUnLevelView p
    v <- reallyUnLevelView v
    match n p v
