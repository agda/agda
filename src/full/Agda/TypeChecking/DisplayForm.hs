{-# LANGUAGE CPP #-}
{-# LANGUAGE UndecidableInstances #-}  -- for Arg a => Elim' a

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

import Agda.Utils.Except
import Agda.Utils.Functor
import Agda.Utils.List
import Agda.Utils.Maybe
import Agda.Utils.Pretty ( prettyShow )

#include "undefined.h"
import Agda.Utils.Impossible

-- | Convert a 'DisplayTerm' into a 'Term'.
dtermToTerm :: DisplayTerm -> Term
dtermToTerm dt = case dt of
  DWithApp d ds es ->
    dtermToTerm d `apply` map (defaultArg . dtermToTerm) ds `applyE` es
  DCon c ci args   -> Con c ci $ map (fmap dtermToTerm) args
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
        "displayForm for " ++ prettyShow q ++ ": context = " ++ show n ++
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
      [ "name        : " ++ prettyShow q
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
      us <- reverse <$> do match ps $ raise 1 es0
      return (d, substWithOrigin (parallelS $ map woThing us) us v `applyE` es1)

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
  match :: a -> a -> MaybeT TCM [WithOrigin Term]

instance Match a => Match [a] where
  match xs ys = concat <$> zipWithM match xs ys

instance Match a => Match (Arg a) where
  match p v = map (setOrigin (getOrigin v)) <$> match (unArg p) (unArg v)

instance Match a => Match (Elim' a) where
  match p v =
    case (p, v) of
      (Proj _ f, Proj _ f') | f == f' -> return []
      (Apply a, Apply a')         -> match a a'
      _                           -> mzero

instance Match Term where
  match p v = lift (instantiate v) >>= \ v -> case (ignoreSharing p, ignoreSharing v) of
    (Var 0 [], v) -> return [ WithOrigin Inserted $ strengthen __IMPOSSIBLE__ v ]
    (Var i ps, Var j vs) | i == j  -> match ps vs
    (Def c ps, Def d vs) | c == d  -> match ps vs
    (Con c _ ps, Con d _ vs) | c == d -> match ps vs
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

-- | Substitute terms with origin into display terms,
--   replacing variables along with their origins.
--
--   The purpose is to replace the pattern variables in a with-display form,
--   and only on the top level of the lhs.  Thus, we are happy to fall back
--   to ordinary substitution where it does not matter.
--   This fixes issue #2590.

class SubstWithOrigin a where
  substWithOrigin :: Substitution -> [WithOrigin Term] -> a -> a

instance SubstWithOrigin a => SubstWithOrigin [a] where
  substWithOrigin rho ots = map (substWithOrigin rho ots)

instance SubstWithOrigin (Arg a) => SubstWithOrigin (Elim' a) where
  substWithOrigin rho ots (Apply arg) = Apply $ substWithOrigin rho ots arg
  substWithOrigin rho ots e@Proj{}    = e

instance SubstWithOrigin (Arg Term) where
  substWithOrigin rho ots (Arg ai v) =
    case ignoreSharing v of
      -- pattern variable: replace origin if better
      Var x [] -> case ots !!! x of
        Just (WithOrigin o u) -> Arg (mapOrigin (replaceOrigin o) ai) u
        Nothing -> __IMPOSSIBLE__
      -- constructor: recurse
      Con c ci args -> Arg ai $ Con c ci $ substWithOrigin rho ots args
      -- def: recurse
      Def q es -> Arg ai $ Def q $ substWithOrigin rho ots es
      -- otherwise: fall back to ordinary substitution
      _ -> Arg ai $ applySubst rho v
    where
      replaceOrigin _ UserWritten = UserWritten
      replaceOrigin o _           = o

instance SubstWithOrigin Term where
  substWithOrigin rho ots v =
    case ignoreSharing v of
      -- constructor: recurse
      Con c ci args -> Con c ci $ substWithOrigin rho ots args
      -- def: recurse
      Def q es -> Def q $ substWithOrigin rho ots es
      -- otherwise: fall back to oridinary substitution
      _ -> applySubst rho v

-- Do not go into dot pattern, otherwise interaction test #231 fails
instance SubstWithOrigin DisplayTerm where
  substWithOrigin rho ots dt =
    case dt of
      DTerm v        -> DTerm     $ substWithOrigin rho ots v
      DDot  v        -> DDot      $ applySubst rho v
      DDef q es      -> DDef q    $ substWithOrigin rho ots es
      DCon c ci args -> DCon c ci $ substWithOrigin rho ots args
      DWithApp t ts es -> DWithApp
        (substWithOrigin rho ots t)
        (substWithOrigin rho ots ts)
        (substWithOrigin rho ots es)

-- Do not go into dot pattern, otherwise interaction test #231 fails
instance SubstWithOrigin (Arg DisplayTerm) where
  substWithOrigin rho ots (Arg ai dt) =
    case dt of
      DTerm v        -> fmap DTerm $ substWithOrigin rho ots $ Arg ai v
      DDot  v        -> Arg ai $ DDot      $ applySubst rho v
      DDef q es      -> Arg ai $ DDef q    $ substWithOrigin rho ots es
      DCon c ci args -> Arg ai $ DCon c ci $ substWithOrigin rho ots args
      DWithApp t ts es -> Arg ai $ DWithApp
        (substWithOrigin rho ots t)
        (substWithOrigin rho ots ts)
        (substWithOrigin rho ots es)
