{-# OPTIONS_GHC -Wunused-imports #-}

{-# LANGUAGE NondecreasingIndentation #-}

-- | Semi-continuity of types in a size variable (issue #8829).
--
--   Recursion on a size that is justified by matching it against a successor
--   @↑ j@ (successor style of sized types, e.g. @suc : ∀ {i} → Nat i → Nat (↑ i)@)
--   amounts to transfinite induction with a limit case.
--   It is only sound if the type of the recursive function is
--   /upper semi-continuous/ in the size,
--   see Andreas Abel, Semi-continuous sized types and termination, LMCS 4(1:3), 2008.
--   (Recursion via @Size<@ style sized types is well-founded recursion
--   that does not need this check.)
--
--   This module implements a conservative syntactic approximation of
--   upper and lower semi-continuity, following the implementation in MiniAgda.
--   It is used by the termination checker ("Agda.Termination.TermCheck")
--   to decide whether a dot pattern @.(↑ j)@ in a size argument may serve as
--   evidence for termination.
--
--   Semantically, a type @A@ depending on size @i@ is
--
--   * /lower semi-continuous/ (LSC) if @A(λ) ⊆ ⋃_{α<λ} ⋂_{α≤i<λ} A(i)@
--     for limit ordinals @λ@, i.e., each element of @A(λ)@ is eventually in @A(i)@;
--
--   * /upper semi-continuous/ (USC) if @⋂_{α<λ} ⋃_{α≤i<λ} A(i) ⊆ A(λ)@,
--     i.e., what is cofinally in @A(i)@ is also in @A(λ)@.
--
--   Rules implemented here:
--
--   * Types not mentioning @i@ are continuous.
--   * Antitone types are LSC, monotone types are USC.
--   * @(x : A) → B@ is USC if @A@ is LSC and @B@ is USC.
--   * @(x : A) → B@ is LSC if @A@ is finite and does not mention @i@, and @B@ is LSC.
--   * @Size< i@ is LSC.
--   * A sized inductive type @D pars i ixs@ (successor style) is LSC.
--   * A data or record type is LSC/USC if all its constructor fields are
--     (for non-recursive data types whose indices do not mention @i@).

module Agda.TypeChecking.SizedTypes.SemiContinuity
  ( admissibleForSizeRecursion
  , upperSemiContinuous
  , lowerSemiContinuous
  , isFiniteType
  ) where

import Prelude hiding (null)

import qualified Data.Set as Set

import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.Syntax.Internal.Names (namesIn)

import Agda.TypeChecking.Free (freeIn)
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Polarity (polarity)
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope

import Agda.Utils.Maybe
import Agda.Utils.Monad

-- | Debug key for this module.
semiContKey :: VerboseKey
semiContKey = "term.size.semicont"

-- | Report a successful rule application (for debugging and test coverage).
yes :: String -> Type -> TCM Bool
yes rule t = do
  reportSDoc semiContKey 20 $ text ("yes (" ++ rule ++ "):") <+> prettyTCM t
  return True

-- | Report a failure.
no :: String -> Type -> TCM Bool
no rule t = do
  reportSDoc semiContKey 20 $ text ("no (" ++ rule ++ "):") <+> prettyTCM t
  return False

-- | Is the given polarity acceptable (monotone resp. antitone)?
type GoodPolarity = Polarity -> Bool

-- | @admissibleForSizeRecursion t@ checks that @t@ is upper semi-continuous
--   in the size variable @0@ (the last variable of the current context).
--   Then @t@ is admissible as type of a recursive function
--   that recurses on this size via successor patterns.
--
--   On failure, returns the reason, in the context of the failure.
admissibleForSizeRecursion :: Type -> TCM (Maybe (Closure SemiContinuityFailure))
admissibleForSizeRecursion t0 = do
  reportSDoc semiContKey 15 $ "admissibleForSizeRecursion" <+> prettyTCM t0
  loop 0 t0
  where
  loop :: Nat -> Type -> TCM (Maybe (Closure SemiContinuityFailure))
  loop i t = ifM (cheapUpper i t) (return Nothing) $ {-else-} do
    t <- reduce t
    case unEl t of
      Pi a b -> do
        ifM (lowerSemiContinuous [] i $ unDom a)
          {-then-} (underAbstractionAbs a b $ loop (i + 1))
          {-else-} (Just <$> buildClosure (NotLowerSemiContinuous (var i) (unDom a)))
      _ -> ifM (upperSemiContinuousStructural [] i t)
          {-then-} (return Nothing)
          {-else-} (Just <$> buildClosure (NotUpperSemiContinuous (var i) t))

-- | Cheap checks for upper semi-continuity:
--   @i@ does not occur or occurs only monotonously.
cheapUpper :: Nat -> Type -> TCM Bool
cheapUpper i t = cheapCheck "USC" (`elem` [Nonvariant, Covariant]) i t

-- | Cheap checks for lower semi-continuity:
--   @i@ does not occur or occurs only antitonously.
cheapLower :: Nat -> Type -> TCM Bool
cheapLower i t = cheapCheck "LSC" (`elem` [Nonvariant, Contravariant]) i t

cheapCheck :: String -> GoodPolarity -> Nat -> Type -> TCM Bool
cheapCheck what good i t
  | not (i `freeIn` t) = yes (what ++ ": size not free") t
  | otherwise = do
      pol <- polarity i t
      if good pol then yes (what ++ ": polarity " ++ show pol) t else return False

-- | @upperSemiContinuous ds i t@ checks that type @t@ is upper
--   semi-continuous in size variable @i@.
--   Data and record types in @ds@ are not unfolded (to prevent looping).
upperSemiContinuous :: [QName] -> Nat -> Type -> TCM Bool
upperSemiContinuous ds i t = cheapUpper i t `or2M` do
  t <- reduce t
  case unEl t of
    Pi a b -> do
      reportSDoc semiContKey 20 $ "USC: function type" <+> prettyTCM t
      lowerSemiContinuous ds i (unDom a) `and2M`
        underAbstractionAbs a b (upperSemiContinuous ds (i + 1))
    _ -> upperSemiContinuousStructural ds i t

-- | Upper semi-continuity of a (reduced) type that is not a function type.
upperSemiContinuousStructural :: [QName] -> Nat -> Type -> TCM Bool
upperSemiContinuousStructural ds i t = case unEl t of
  Def d es -> dataSemiContinuous "USC" upperSemiContinuous ds i d es t
  _ -> no "USC: not a data or record type" t

-- | @lowerSemiContinuous ds i t@ checks that type @t@ is lower
--   semi-continuous in size variable @i@.
--   Data and record types in @ds@ are not unfolded (to prevent looping).
lowerSemiContinuous :: [QName] -> Nat -> Type -> TCM Bool
lowerSemiContinuous ds i t = cheapLower i t `or2M` do
  t <- reduce t
  case unEl t of

    -- @(x : A) → B@ is LSC if @A@ is finite and constant and @B@ is LSC.
    -- (Finite intersections of LSC sets are LSC.)
    Pi a b
      | i `freeIn` a -> no "LSC: function domain mentions size" t
      | otherwise -> do
          ifNotM (isFiniteDom a) (no "LSC: function domain not finite" t) $ {-else-} do
            reportSDoc semiContKey 20 $ "LSC: function type with finite domain" <+> prettyTCM t
            underAbstractionAbs a b $ lowerSemiContinuous ds (i + 1)

    Def d es -> isSizeType t >>= \case

      -- @Size< i@ is LSC.
      Just (BoundedLt u) -> reduce u >>= \case
        Var j [] | j == i -> yes "LSC: Size< i" t
        _ -> no "LSC: bounded size type" t

      _ -> ifM (sizedInductiveTypeAt i d es) (yes "LSC: sized inductive type" t) $ {-else-}
        dataSemiContinuous "LSC" lowerSemiContinuous ds i d es t

    _ -> no "LSC: no rule applies" t

-- | Is the domain of a function type finite?
--   Covers irrelevant domains, domains in @Prop@ (subsingletons),
--   the faces of cubical 'Partial' elements ('domIsFinite'),
--   and finite data and record types.
isFiniteDom :: Dom Type -> TCM Bool
isFiniteDom a
  | domIsFinite a = yesFin "IsOne domain"
  | isIrrelevant a = yesFin "irrelevant domain"
  | otherwise = isFiniteType [] (unDom a)
  where yesFin s = yes ("finite: " ++ s) (unDom a)

-- | @isFiniteType ds t@ is a conservative check whether type @t@ has
--   finitely many elements (in each instance of its free variables).
--   Data and record types in @ds@ are not unfolded (to prevent looping).
isFiniteType :: [QName] -> Type -> TCM Bool
isFiniteType ds t = do
  t <- reduce t
  s <- reduce $ getSort t
  if isProp s then yes "finite: Prop" t else do
  case unEl t of
    Def d es
      | d `elem` ds -> no "finite: recursive data type" t
      | otherwise   -> fromMaybeM (no "finite: not a data or record type" t) $
          forConstructorFields d es $ \ _np _ixs tels -> do
            ifNotM (andM $ map (allTel (const isFiniteField) 0) tels)
              {-then-} (no "finite: field not finite" t)
              {-else-} (yes "finite: data or record type" t)
          where
          isFiniteField :: Dom Type -> TCM Bool
          isFiniteField a
            | isIrrelevant a = return True
            | otherwise      = isFiniteType (d : ds) (unDom a)
    _ -> no "finite: not a data or record type" t

-- | @dataSemiContinuous what check ds i d es t@ checks that
--   data or record type @t = d es@ is semi-continuous in @i@
--   by checking all constructor fields with @check@.
--
--   Fails if @d ∈ ds@ (recursive occurrence)
--   or if the indices of @d es@ mention @i@.
dataSemiContinuous
  :: String
  -> ([QName] -> Nat -> Type -> TCM Bool)
  -> [QName] -> Nat -> QName -> Elims -> Type -> TCM Bool
dataSemiContinuous what check ds i d es t
  | d `elem` ds = no (what ++ ": recursive data type") t
  | otherwise = fromMaybeM (no (what ++ ": not a data or record type") t) $
      forConstructorFields d es $ \ _np ixs tels -> do
        if i `freeIn` ixs then no (what ++ ": size in data index") t else do
        ifNotM (andM $ map (allTel (\ j a -> check (d : ds) j (unDom a)) i) tels)
          {-then-} (no (what ++ ": constructor field") t)
          {-else-} (yes (what ++ ": data or record type") t)

-- | @allTel check i tel@ checks all types of telescope @tel@,
--   where @i@ is a de Bruijn index in the context of @tel@
--   (raised as we go under binders).
allTel :: (Nat -> Dom Type -> TCM Bool) -> Nat -> Telescope -> TCM Bool
allTel check i = \case
  EmptyTel        -> return True
  ExtendTel a tel -> check i a `and2M` underAbstractionAbs a tel (allTel check (i + 1))

-- | @forConstructorFields d es k@:
--   If @d es@ is a data or record type with parameters @pars@ and indices @ixs@,
--   call @k np ixs tels@ where @tels@ are the field telescopes
--   of the constructors, instantiated to the parameters.
--   Otherwise return 'Nothing'.
forConstructorFields
  :: QName -> Elims
  -> (Nat -> Elims -> [Telescope] -> TCM a)
  -> TCM (Maybe a)
forConstructorFields d es k = do
  def <- getConstInfo d
  let
    run np cs = do
      let (pars, ixs) = splitAt np es
      caseMaybe (allApplyElims pars) (return Nothing) $ \ pars -> do
        tels <- forM cs $ \ c -> do
          ct <- defType <$> getConstInfo c
          TelV tel _ <- telView =<< ct `piApplyM` pars
          return tel
        Just <$> k np ixs tels
  case theDef def of
    Datatype{ dataPars = np, dataCons = cs } -> run np cs
    Record{ recPars = np, recConHead = c }   -> run np [conName c]
    _ -> return Nothing

-- | @sizedInductiveTypeAt i d es@ checks that @d es@ is a sized inductive
--   data type in successor style whose size index is the variable @i@
--   (and @i@ does not occur otherwise).
--
--   We rely on the size polarity check ('Agda.TypeChecking.Polarity.sizePolarity')
--   which ensures that the size index is used as in
--   @c : ∀ {j} → ... D j ... → D (↑ j)@ (only covariantly in the arguments).
--   Sized data types using the musical @∞@ are coinductive and thus excluded.
sizedInductiveTypeAt :: Nat -> QName -> Elims -> TCM Bool
sizedInductiveTypeAt i d es = do
  def <- getConstInfo d
  case theDef def of
    Datatype{ dataPars = np, dataCons = cs } | (pars, Apply ix : ixs) <- splitAt np es -> do
      ix <- reduce $ unArg ix
      case ix of
        Var j [] | j == i, not (i `freeIn` (pars, ixs)) -> do
          -- The first index must be of type Size.
          TelV tel _ <- telView $ defType def
          isSize <- caseMaybe (listToMaybe $ drop np $ telToList tel) (return False) $ \ a ->
            (Just BoundedNo ==) <$> isSizeType (snd <$> a)
          -- The size index must have been found covariant by the size polarity check.
          pols <- getPolarity d
          let covariant = listToMaybe (drop np pols) == Just Covariant
          -- The data type must not use musical coinduction.
          minf <- getBuiltinName' builtinInf
          coind <- caseMaybe minf (return False) $ \ inf ->
            (`anyM` cs) $ \ c -> Set.member inf . namesIn . defType <$> getConstInfo c
          return $ isSize && covariant && not coind
        _ -> return False
    _ -> return False
