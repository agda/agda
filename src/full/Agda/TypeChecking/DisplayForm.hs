{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}

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

import Agda.Utils.List
import Agda.Utils.Maybe

#include "../undefined.h"
import Agda.Utils.Impossible

-- | Find a matching display form for @q vs@.
--   In essence this tries to reqwrite @q vs@ with any
--   display form @q ps --> dt@ and returns the instantiated
--   @dt@ if successful.  First match wins.
displayForm :: QName -> Args -> TCM (Maybe DisplayTerm)
displayForm q vs = do
    -- Get display forms for name q.
    odfs  <- defDisplay <$> getConstInfo q
    -- Display debug info about the @Open@s.
    unless (null odfs) $ verboseS "tc.display.top" 100 $ do
      n <- getContextId
      reportSLn "tc.display.top" 100 $
        "displayForm: context = " ++ show n ++
        ", dfs = " ++ show (map openThingCtxIds odfs)
    -- Use only the display forms that can be opened in the current context.
    dfs	  <- catMaybes <$> mapM tryOpen odfs
    scope <- getScope
    -- Keep the display forms that match the application @c vs@.
    ms <- do
      ms <- mapM (runMaybeT . (`matchDisplayForm` vs)) dfs
      return [ m | Just m <- ms, inScope scope m ]
    -- Not safe when printing non-terminating terms.
    -- (nfdfs, us) <- normalise (dfs, vs)
    unless (null odfs) $ reportSLn "tc.display.top" 100 $ unlines
      [ "name        : " ++ show q
      , "displayForms: " ++ show dfs
      , "arguments   : " ++ show vs
      , "matches     : " ++ show ms
      , "result      : " ++ show (foldr (const . Just) Nothing ms)
      ]
    -- Return the first display form that matches.
    return $ mhead ms

--  Andreas, 2014-06-11: The following error swallowing
--  is potentially harmful, making debugging harder.
--  I removed it, and it does not cause problems on the test suite.
--  `catchError` \_ -> return Nothing

  where
    inScope _ _ = True  -- TODO: distinguish between with display forms and other display forms
--     inScope scope d = case hd d of
--       Just h  -> isJust $ inverseScopeLookupName h scope
--       Nothing -> __IMPOSSIBLE__ -- TODO: currently all display forms have heads
    -- 'hd' is only used in the commented-out code for 'inScope' above.
    -- hd (DTerm (Def x _))    = Just x
    -- hd (DTerm (Con x _))    = Just $ conName x
    -- hd (DTerm (Shared p))   = hd (DTerm $ derefPtr p)
    -- hd (DWithApp d _ _) = hd d
    -- hd _		    = Nothing

-- | Match a 'DisplayForm' @q ps = v@ against @q vs@.
--   Return the 'DisplayTerm' @v[us]@ if the match was successful,
--   i.e., @vs / ps = Just us@.
matchDisplayForm :: DisplayForm -> Args -> MaybeT TCM DisplayTerm
matchDisplayForm (Display _ ps v) vs
  | length ps > length vs = mzero
  | otherwise             = do
      us <- match ps $ raise 1 $ map unArg vs0
      return $ applySubst (parallelS $ reverse us) v `apply` vs1
  where
    (vs0, vs1) = splitAt (length ps) vs

-- | Class @Match@ for matching a term @p@ in the role of a pattern
--   against a term @v@.
--
--   The 0th variable in @p@ plays the role
--   of a place holder (pattern variable).  Each occurrence of
--   @var 0@ in @p@ stands for a different pattern variable.
--
--   The result of matching, if successful, is a list of solutions for the
--   pattern variables, in left-to-right order.
--
--   The 0th variable is in scope in the input @v@, but should not
--   actually occur!
--   In the output solution, the @0th@ variable is no longer in scope.
--   (It has been substituted by __IMPOSSIBLE__ which corresponds to
--   a raise by -1).
class Match a where
  match :: a -> a -> MaybeT TCM [Term]

instance Match a => Match [a] where
  match xs ys = concat <$> zipWithM match xs ys

instance Match a => Match (Arg a) where
  match p v = match (unArg p) (unArg v)

instance Match a => Match (Elim' a) where
  match p v =
    case (p, v) of
      (Proj f, Proj f') | f == f' -> return []
      (Apply a, Apply a')         -> match a a'
      _                           -> mzero

instance Match Term where
  match p v = case (ignoreSharing p, ignoreSharing v) of
    (Var 0 [], v)                  -> return [subst __IMPOSSIBLE__ v]
    (Var i ps, Var j vs) | i == j  -> match ps vs
    (Def c ps, Def d vs) | c == d  -> match ps vs
    (Con c ps, Con d vs) | c == d  -> match ps vs
    (Lit l, Lit l')      | l == l' -> return []
    (p, v)               | p == v  -> return []
    (p, Level l)                   -> match p =<< reallyUnLevelView l
    (Sort ps, Sort pv)             -> match ps pv
    (p, Sort (Type v))             -> match p =<< reallyUnLevelView v
    _                              -> mzero

instance Match Sort where
  match p v = case (p, v) of
    (Type pl, Type vl) -> match pl vl
    _ | p == v -> return []
    _          -> mzero

instance Match Level where
  match p v = do
    p <- reallyUnLevelView p
    v <- reallyUnLevelView v
    match p v
