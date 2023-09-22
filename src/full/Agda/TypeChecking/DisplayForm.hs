{-# LANGUAGE UndecidableInstances #-}  -- for Arg a => Elim' a

-- | Tools for 'DisplayTerm' and 'DisplayForm'.

module Agda.TypeChecking.DisplayForm (displayForm) where

import Control.Monad
import Control.Monad.Trans (lift)
import Control.Monad.Trans.Maybe

import Data.Monoid (All(..))
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Set as Set

import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.Syntax.Internal.Names
import Agda.Syntax.Scope.Base (inverseScopeLookupName)

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Level
import Agda.TypeChecking.Reduce (instantiate)

import Agda.Utils.Functor
import Agda.Utils.List
import Agda.Utils.Maybe
import Agda.Syntax.Common.Pretty

import Agda.Utils.Impossible

-- | Get the arities of all display forms for a name.
displayFormArities :: (HasConstInfo m, ReadTCState m) => QName -> m [Int]
displayFormArities q = map (length . dfPats . dget) <$> getDisplayForms q

-- | Lift a local display form to an outer context. The substitution goes from the parent context to
--   the context of the local display form (see Issue 958). Current only handles pure extensions of
--   the parent context.
liftLocalDisplayForm :: Substitution -> DisplayForm -> Maybe DisplayForm
liftLocalDisplayForm IdS df = Just df
liftLocalDisplayForm (Wk n IdS) (Display m lhs rhs) =
  -- We lift a display form by turning matches on free variables into pattern variables, which can
  -- be done by simply adding to the dfPatternVars field.
  Just $ Display (n + m) lhs rhs
liftLocalDisplayForm _ _ = Nothing

type MonadDisplayForm m =
  ( MonadReduce m
  , ReadTCState m
  , HasConstInfo m
  , HasBuiltins m
  , MonadDebug m
  )

-- | Find a matching display form for @q es@.
--   In essence this tries to rewrite @q es@ with any
--   display form @q ps --> dt@ and returns the instantiated
--   @dt@ if successful.  First match wins.
displayForm :: MonadDisplayForm m => QName -> Elims -> m (Maybe DisplayTerm)
displayForm q es = do
  -- Get display forms for name q.
  odfs  <- getDisplayForms q
  if (null odfs) then do
    reportSLn "tc.display.top" 101 $ "no displayForm for " ++ prettyShow q
    return Nothing
  else do
    -- Display debug info about the @Open@s.
    unlessDebugPrinting $ reportSDoc "tc.display.top" 100 $ do
      cps <- viewTC eCheckpoints
      cxt <- getContextTelescope
      return $ vcat
        [ "displayForm for" <+> pretty q
        , nest 2 $ "cxt =" <+> pretty cxt
        , nest 2 $ "cps =" <+> vcat (map pretty (Map.toList cps))
        , nest 2 $ "dfs =" <+> vcat (map pretty odfs) ]
    -- Use only the display forms that can be opened in the current context.
    dfs   <- catMaybes <$> mapM (tryGetOpen liftLocalDisplayForm) odfs
    scope <- getScope
    -- Keep the display forms that match the application @q es@.
    ms <- do
      ms <- mapM (runMaybeT . (`matchDisplayForm` es)) dfs
      return [ m | Just (d, m) <- ms, wellScoped scope d ]
    -- Not safe when printing non-terminating terms.
    -- (nfdfs, us) <- normalise (dfs, es)
    unlessDebugPrinting $ reportSDoc "tc.display.top" 100 $ return $ vcat
      [ "name        :" <+> pretty q
      , "displayForms:" <+> pretty dfs
      , "arguments   :" <+> pretty es
      , "matches     :" <+> pretty ms
      , "result      :" <+> pretty (listToMaybe ms)
      ]
    -- Return the first display form that matches.
    return $ listToMaybe ms
  where
    -- Look at the original display form, not the instantiated result when
    -- checking if it's well-scoped. Otherwise we might pick up out of scope
    -- identifiers coming from the source term.
    wellScoped scope (Display _ _ d)
      | isWithDisplay d = True
      | otherwise       = getAll $ namesIn' (All . inScope scope) d  -- all names in d should be in scope

    inScope scope x = not $ null $ inverseScopeLookupName x scope

    isWithDisplay DWithApp{} = True
    isWithDisplay _          = False

-- | Match a 'DisplayForm' @q ps = v@ against @q es@.
--   Return the 'DisplayTerm' @v[us]@ if the match was successful,
--   i.e., @es / ps = Just us@.
matchDisplayForm :: MonadDisplayForm m
                 => DisplayForm -> Elims -> MaybeT m (DisplayForm, DisplayTerm)
matchDisplayForm d@(Display n ps v) es
  | length ps > length es = mzero
  | otherwise             = do
      let (es0, es1) = splitAt (length ps) es
      mm <- match (Window 0 n) ps es0
      us <- forM [0 .. n - 1] $ \ i -> do
              -- #5294: Fail if we don't have bindings for all variables. This can
              --        happen outside parameterised modules when some of the parameters
              --        are not used in the lhs.
              Just u <- return $ Map.lookup i mm
              return u
      return (d, substWithOrigin (parallelS $ map woThing us) us v `applyE` es1)

type MatchResult = Map Int (WithOrigin Term)

unionMatch :: Monad m => MatchResult -> MatchResult -> MaybeT m MatchResult
unionMatch m1 m2
  | null (Map.intersection m1 m2) = return $ Map.union m1 m2
  | otherwise = mzero  -- Non-linear pattern, fail for now.

unionsMatch :: Monad m => [MatchResult] -> MaybeT m MatchResult
unionsMatch = foldM unionMatch Map.empty

data Window = Window {dbLo, dbHi :: Nat}

inWindow :: Window -> Nat -> Maybe Nat
inWindow (Window lo hi) n | lo <= n, n < hi = Just (n - lo)
                          | otherwise       = Nothing

shiftWindow :: Window -> Window
shiftWindow (Window lo hi) = Window (lo + 1) (hi + 1)

-- | Class @Match@ for matching a term @p@ in the role of a pattern
--   against a term @v@.
--
--   Free variables inside the window in @p@ are pattern variables and
--   the result of matching is a map from pattern variables (shifted down to start at 0) to subterms
--   of @v@.
class Match a where
  match :: MonadDisplayForm m => Window -> a -> a -> MaybeT m MatchResult

instance Match a => Match [a] where
  match n xs ys = unionsMatch =<< zipWithM (match n) xs ys

instance Match a => Match (Arg a) where
  match n p v = Map.map (setOrigin (getOrigin v)) <$> match n (unArg p) (unArg v)

instance Match a => Match (Elim' a) where
  match n p v =
    case (p, v) of
      (Proj _ f, Proj _ f') | f == f' -> return Map.empty
      _ | Just a  <- isApplyElim p
        , Just a' <- isApplyElim v    -> match n a a'
      -- we do not care to differentiate between Apply and IApply for
      -- printing.
      _                               -> mzero

instance Match Term where
  match w p v = lift (instantiate v) >>= \ v -> case (unSpine p, unSpine v) of
    (Var i [], v)    | Just j <- inWindow w i -> return $ Map.singleton j (WithOrigin Inserted v)
    (Var i (_:_), v) | Just{} <- inWindow w i -> mzero  -- Higher-order pattern, fail for now.
    (Var i ps, Var j vs) | i == j  -> match w ps vs
    (Def c ps, Def d vs) | c == d  -> match w ps vs
    (Con c _ ps, Con d _ vs) | c == d -> match w ps vs
    (Lit l, Lit l')      | l == l' -> return Map.empty
    (Lam h p, Lam h' v)  | h == h' -> match (shiftWindow w) (unAbs p) (unAbs v)
    (p, v)               | p == v  -> return Map.empty  -- TODO: this is wrong (this is why we lifted the rhs before)
    (p, Level l)                   -> match w p =<< reallyUnLevelView l
    (Sort ps, Sort pv)             -> match w ps pv
    (p, Sort (Type v))             -> match w p =<< reallyUnLevelView v
    _                              -> mzero

instance Match Sort where
  match w p v = case (p, v) of
    (Type pl, Type vl) -> match w pl vl
    _ | p == v -> return Map.empty
    _          -> mzero

instance Match Level where
  match w p v = do
    p <- reallyUnLevelView p
    v <- reallyUnLevelView v
    match w p v

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

instance (SubstWithOrigin a, SubstWithOrigin (Arg a)) => SubstWithOrigin (Elim' a) where
  substWithOrigin rho ots (Apply arg) = Apply $ substWithOrigin rho ots arg
  substWithOrigin rho ots e@Proj{}    = e
  substWithOrigin rho ots (IApply u v w) = IApply
    (substWithOrigin rho ots u)
    (substWithOrigin rho ots v)
    (substWithOrigin rho ots w)



instance SubstWithOrigin (Arg Term) where
  substWithOrigin rho ots (Arg ai v) =
    case v of
      -- pattern variable: replace origin if better
      Var x [] -> case ots !!! x of
        Just (WithOrigin o u) -> Arg (mapOrigin (replaceOrigin o) ai) u
        Nothing -> Arg ai $ applySubst rho v -- Issue #2717, not __IMPOSSIBLE__
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
    case v of
      -- constructor: recurse
      Con c ci args -> Con c ci $ substWithOrigin rho ots args
      -- def: recurse
      Def q es -> Def q $ substWithOrigin rho ots es
      -- otherwise: fall back to oridinary substitution
      _ -> applySubst rho v

-- Do not go into dot pattern, otherwise interaction test #231 fails
instance SubstWithOrigin DisplayTerm where
  substWithOrigin rho ots =
    \case
      DTerm' v es    -> DTerm' (substWithOrigin rho ots v) $ substWithOrigin rho ots es
      DDot'  v es    -> DDot'  (substWithOrigin rho ots v) $ substWithOrigin rho ots es
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
      DTerm' v es    -> substWithOrigin rho ots (Arg ai v) <&> (`DTerm'` substWithOrigin rho ots es)
      DDot'  v es    -> Arg ai $ DDot' (applySubst rho v)  $ substWithOrigin rho ots es
      DDef q es      -> Arg ai $ DDef q    $ substWithOrigin rho ots es
      DCon c ci args -> Arg ai $ DCon c ci $ substWithOrigin rho ots args
      DWithApp t ts es -> Arg ai $ DWithApp
        (substWithOrigin rho ots t)
        (substWithOrigin rho ots ts)
        (substWithOrigin rho ots es)
