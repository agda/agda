{-# OPTIONS_GHC -Wunused-imports #-}

-- | Termination checking: functionality specific to sized types.
--
--   Issue #8829: A dot pattern @.(↑ j)@ in a size argument
--   (arising from matching on a successor-style sized data type,
--   e.g. @suc : ∀ {i} → Nat i → Nat (↑ i)@)
--   is treated by the termination checker like a constructor pattern,
--   providing termination evidence for calls with argument @j@.
--   This amounts to transfinite induction on sizes and is only sound
--   if the type of the function is upper semi-continuous in this size
--   (see "Agda.TypeChecking.SizedTypes.SemiContinuity").
--   Recursion via @Size<@ is well-founded and does not need this check;
--   it does not produce successor patterns.
--
--   The verdicts are precomputed per mutual block ('buildSizeSucVerdicts'),
--   only for argument positions that actually hold a successor pattern,
--   and only if sized types are enabled.

module Agda.Termination.SizedTypes
  ( buildSizeSucVerdicts
  , revertInadmissibleSizeSuc
  , terGetInadmissibleSizes
  , reduceDotPatternTerm
  , isSizeSucApp
  , maskSizeLt
  ) where

import Prelude hiding (null)

import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set

import Agda.Syntax.Common
import Agda.Syntax.Internal

import Agda.Termination.Monad

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Records
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.SizedTypes.SemiContinuity ( admissibleForSizeRecursion )
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope

import Agda.Utils.List
import Agda.Utils.Maybe
import Agda.Utils.Monad
import Agda.Utils.Null

import Agda.Utils.Impossible

-- | Issue #8829: A dot pattern @.(↑ j)@ in a size argument of function @f@
--   is turned into a constructor-like pattern by 'termToPattern',
--   providing termination evidence for calls with argument @j@.
--   This is only sound if the type of @f@ is admissible for recursion on this size,
--   i.e., upper semi-continuous in the size.
--   Otherwise, we revert these patterns to dot patterns.
--
--   The admissibility check is only invoked if there is such a successor pattern.
--   It is not needed for sizes in @Size<@ style, as these do not lead to successor patterns.
revertInadmissibleSizeSuc
  :: QName                     -- ^ The function @f@.
  -> [QName]                   -- ^ The projection path of the clause.
  -> NAPs                      -- ^ Original patterns of the clause.
  -> NAPs                      -- ^ Patterns after parsing dot patterns ('parseDotP').
  -> TerM NAPs
revertInadmissibleSizeSuc f path ps0 ps = do
  suc <- terGetSizeSuc
  let
    isSuc p = case namedArg p of
      ConP c _ _ -> Just (conName c) == suc
      _ -> False
    slots = [ k | (k, p) <- zip [0..] ps, isSuc p ]
  if null slots then return ps else do
    bad <- filterM (fmap not . sizeSucAdmissible f path) slots
    return $ zipWith3 (\ k p0 p -> if k `elem` bad then p0 else p) [0..] ps0 ps

-- | Is a successor pattern at the given argument position (counting projection patterns)
--   of a clause of function @f@ admissible as termination evidence?
--   Looks up the verdict precomputed by 'buildSizeSucVerdicts'.
--   A missing verdict counts as inadmissible.
sizeSucAdmissible :: QName -> [QName] -> Int -> TerM Bool
sizeSucAdmissible f path k = do
  Map.lookup (f, path, k) <$> terGetSizeSucVerdicts >>= \case
    Just SizeSucAdmissible     -> return True
    Just SizeSucInadmissible{} -> return False
    Nothing -> do
      reportSDoc "term.size.semicont" 10 $
        "no precomputed verdict for successor pattern in argument" <+> text (show k) <+>
        "of" <+> prettyTCM f <+> "(treating as inadmissible)"
      return False

-- | Issue #8829: Precompute, for the functions of a mutual block,
--   the admissibility of successor patterns (see 'revertInadmissibleSizeSuc').
--
--   Only argument positions in which a clause has a dot pattern @.(↑ j)@
--   are checked, and only if sized types are enabled.
--   The detection of these dot patterns ('isSizeSucDotPattern') must agree
--   with 'termToPattern', otherwise we lose precision (but not soundness).
buildSizeSucVerdicts :: Set QName -> TCM SizeSucVerdicts
buildSizeSucVerdicts allNames = sizeSucName >>= \case
  Nothing  -> return Map.empty
  Just suc -> Map.fromList . concat <$> do
    forM (Set.toList allNames) $ \ f -> inConcreteOrAbstractMode f \ def -> do
      -- Collect the successor slots of all clauses.
      slots <- forM (defClauses def) $ \ cl -> do
        let ps = namedClausePats cl
        path <- mapM getOriginalProjection $
          mapMaybe (fmap (headAmbQ . snd) . isProjP . namedArg) ps
        ks <- addContext (clauseTel cl) $
          map fst <$> filterM (isSizeSucDotPattern suc . namedArg . snd) (zip [0..] ps)
        return [ ((path, k), ps) | k <- ks ]
      -- Check each slot once.
      forM (nubOn fst $ concat slots) $ \ ((path, k), ps) ->
        ((f, path, k),) <$> inTopContext (sizeSucVerdict f ps k)
  where
  isSizeSucDotPattern :: QName -> DeBruijnPattern -> TCM Bool
  isSizeSucDotPattern suc = \case
    DotP _ t -> isSizeSucApp suc <$> reduceDotPatternTerm t
    _ -> return False

-- | Reduce the term of a dot pattern for conversion into a pattern.
reduceDotPatternTerm :: (MonadReduce m, HasBuiltins m) => Term -> m Term
reduceDotPatternTerm t = constructorForm =<< reduce t

-- | Is the (reduced) term an application of @SIZESUC@?
isSizeSucApp :: QName -> Term -> Bool
isSizeSucApp suc = \case
  Def s [Apply _] -> s == suc
  _ -> False

-- | Check the admissibility of the type of function @f@ for successor patterns
--   at the given argument position (counting projection patterns),
--   following the patterns of a clause to find the position.
--   To be run in the top context.
sizeSucVerdict :: QName -> NAPs -> Int -> TCM SizeSucVerdict
sizeSucVerdict f ps0 k0 = do
  reportSDoc "term.size.semicont" 10 $ vcat
    [ "checking admissibility of type of" <+> prettyTCM f
    , "for successor patterns in argument" <+> text (show k0)
    ]
  t <- defType <$> getConstInfo f
  walk t ps0 k0
  where
  -- Find the type at position k, following the patterns.
  walk :: Type -> NAPs -> Int -> TCM SizeSucVerdict
  walk t ps k = do
    t <- reduce t
    case (ps, unEl t) of
      (p : ps, _) | ProjP _ q <- namedArg p ->
        getDefType q t >>= \case
          Just projTy -> reduce projTy >>= \case
            El _ (Pi a b) -> underAbstractionAbs a b $ \ t -> walk t ps (k - 1)
            _ -> giveUp
          Nothing -> giveUp
      (_ : _, Pi a b)
        | k == 0 -> do
            r <- underAbstractionAbs a b admissibleForSizeRecursion
            reportSDoc "term.size.semicont" 10 $
              "admissible:" <+> text (show $ isNothing r)
            return $ maybe SizeSucAdmissible (SizeSucInadmissible . Just) r
        | otherwise -> underAbstractionAbs a b $ \ t -> walk t (drop 1 ps) (k - 1)
      _ -> giveUp
  giveUp = return $ SizeSucInadmissible Nothing

-- | Collect the reasons for inadmissible successor patterns.
terGetInadmissibleSizes :: TerM [InadmissibleSize]
terGetInadmissibleSizes = do
  m <- terGetSizeSucVerdicts
  -- Report with-functions under the name of their parent function.
  xs <- liftTCM $ forM [ (f, cl) | ((f, _, _), SizeSucInadmissible (Just cl)) <- Map.toList m ] $
    \ (f, cl) -> (`InadmissibleSize` cl) <$> parentFunction f
  return $ nubOn inadmFunction xs
  where
  parentFunction :: QName -> TCM QName
  parentFunction f = theDef <$> getConstInfo f >>= \case
    Function{ funWith = WithFunction g } -> parentFunction g
    _ -> return f


-- | Rewrite type @tel -> Size< u@ to @tel -> Size@.
maskSizeLt :: MonadTCM tcm => Dom Type -> tcm (Dom Type)
maskSizeLt !dom = liftTCM $ do
  let a = unDom dom
  (msize, msizelt) <- getBuiltinSize
  case (msize, msizelt) of
    (_ , Nothing) -> return dom
    (Nothing, _)  -> __IMPOSSIBLE__
    (Just size, Just sizelt) -> do
      TelV tel c <- telView a
      case a of
        El s (Def d [v]) | d == sizelt -> return $
          abstract tel (El s $ Def size []) <$ dom
        _ -> return dom

