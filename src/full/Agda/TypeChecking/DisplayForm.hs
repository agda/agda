{-# LANGUAGE CPP #-}

-- | Tools for 'DisplayTerm' and 'DisplayForm'.

module Agda.TypeChecking.DisplayForm where

import Prelude hiding (all)
import Control.Applicative
import Control.Monad
import Control.Monad.Trans (lift)
import Control.Monad.Trans.Maybe
import Data.Foldable (all)
import qualified Data.Set as Set

import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.Syntax.Internal.Names
import Agda.Syntax.Scope.Base (inverseScopeLookupName)

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Level
import Agda.TypeChecking.Reduce (instantiate)

import Agda.Utils.List
import Agda.Utils.Maybe
import Agda.Utils.Except
import Agda.Utils.Functor

#include "undefined.h"
import Agda.Utils.Impossible

-- | Convert a 'DisplayTerm' into a 'Term'.
dtermToTerm :: DisplayTerm -> Term
dtermToTerm dt = case dt of
  DWithApp d ds es ->
    dtermToTerm d `apply` map (defaultArg . dtermToTerm) ds `applyE` es
  DCon c args      -> Con c $ map (fmap dtermToTerm) args
  DDef f es        -> Def f $ map (fmap dtermToTerm) es
  DDot v           -> v
  DTerm v          -> v

-- | Get the arities of all display forms for a name.
displayFormArities :: QName -> TCM [Int]
displayFormArities q = map (length . dfPats . dget) <$> getDisplayForms q

-- | Find a matching display form for @q es@.
--   In essence this tries to rewrite @q es@ with any
--   display form @q ps --> dt@ and returns the instantiated
--   @dt@ if successful.  First match wins.
displayForm :: QName -> Elims -> TCM (Maybe DisplayTerm)
displayForm q es = do
    -- Get display forms for name q.
    odfs  <- getDisplayForms q `catchError` \_ -> return []
    -- Display debug info about the @Open@s.
    unless (null odfs) $ verboseS "tc.display.top" 100 $ do
      n <- getContextId
      reportSLn "tc.display.top" 100 $
        "displayForm for " ++ show q ++ ": context = " ++ show n ++
        ", dfs = " ++ show odfs
    -- Use only the display forms that can be opened in the current context.
    dfs   <- catMaybes <$> mapM getLocal odfs
    scope <- getScope
    -- Keep the display forms that match the application @q es@.
    ms <- do
      ms <- mapM (runMaybeT . (`matchDisplayForm` es)) dfs
      return [ m | Just (d, m) <- ms, wellScoped scope d ]
    -- Not safe when printing non-terminating terms.
    -- (nfdfs, us) <- normalise (dfs, es)
    unless (null odfs) $ reportSLn "tc.display.top" 100 $ unlines
      [ "name        : " ++ show q
      , "displayForms: " ++ show dfs
      , "arguments   : " ++ show es
      , "matches     : " ++ show ms
      , "result      : " ++ show (headMaybe ms)
      ]
    -- Return the first display form that matches.
    return $ headMaybe ms

--  Andreas, 2014-06-11: The following error swallowing
--  is potentially harmful, making debugging harder.
--  I removed it, and it does not cause problems on the test suite.
--  `catchError` \_ -> return Nothing

  where
    -- Look at the original display form, not the instantiated result when
    -- checking if it's well-scoped. Otherwise we might pick up out of scope
    -- identifiers coming from the source term.
    wellScoped scope (Display _ _ d)
      | isWithDisplay d = True
      | otherwise       = all (inScope scope) $ namesIn d

    inScope scope x = not $ null $ inverseScopeLookupName x scope

    isWithDisplay DWithApp{} = True
    isWithDisplay _          = False

-- | Match a 'DisplayForm' @q ps = v@ against @q es@.
--   Return the 'DisplayTerm' @v[us]@ if the match was successful,
--   i.e., @es / ps = Just us@.
matchDisplayForm :: DisplayForm -> Elims -> MaybeT TCM (DisplayForm, DisplayTerm)
matchDisplayForm d@(Display _ ps v) es
  | length ps > length es = mzero
  | otherwise             = do
      let (es0, es1) = splitAt (length ps) es
      us <- match ps $ raise 1 es0
      return (d, applySubst (parallelS $ reverse us) v `applyE` es1)

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
      (Proj _ f, Proj _ f') | f == f' -> return []
      (Apply a, Apply a')         -> match a a'
      _                           -> mzero

instance Match Term where
  match p v = lift (instantiate v) >>= \ v -> case (ignoreSharing p, ignoreSharing v) of
    (Var 0 [], v)                  -> return [strengthen __IMPOSSIBLE__ v]
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
