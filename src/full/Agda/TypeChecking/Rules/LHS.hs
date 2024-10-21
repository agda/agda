{-# LANGUAGE NondecreasingIndentation #-}

module Agda.TypeChecking.Rules.LHS
  ( checkLeftHandSide
  , LHSResult(..)
  , bindAsPatterns
  , IsFlexiblePattern(..)
  , DataOrRecord
  , checkSortOfSplitVar
  ) where

import Prelude hiding ( null )

import Data.Function (on)
import Data.Maybe

import Control.Arrow (left)
import Control.Monad.Except       ( MonadError(..), ExceptT(..), runExceptT )
import Control.Monad.Reader       ( MonadReader(..), asks, runReaderT )
import Control.Monad.Writer       ( MonadWriter(..), runWriterT )
import Control.Monad.Trans.Maybe

import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.List (findIndex)
import qualified Data.List as List
import Data.Semigroup ( Semigroup )
import qualified Data.Semigroup as Semigroup
import Data.Map (Map)
import qualified Data.Map as Map

import Agda.Interaction.Highlighting.Generate
  ( storeDisambiguatedConstructor, storeDisambiguatedProjection, disambiguateRecordFields)
import Agda.Interaction.Options
import Agda.Interaction.Options.Lenses

import Agda.Syntax.Internal as I hiding (DataOrRecord)
import Agda.Syntax.Internal.Pattern
import qualified Agda.Syntax.Abstract as A
import Agda.Syntax.Abstract.Views (asView, deepUnscope)
import Agda.Syntax.Concrete (FieldAssignment'(..),LensInScope(..))
import Agda.Syntax.Common as Common
import qualified Agda.Syntax.Info as A
import Agda.Syntax.Literal
import Agda.Syntax.Position

import Agda.TypeChecking.Monad

import qualified Agda.TypeChecking.Monad.Benchmark as Bench
import Agda.TypeChecking.Conversion
import Agda.TypeChecking.Constraints
import Agda.TypeChecking.CheckInternal (checkInternal)
import Agda.TypeChecking.Datatypes hiding (isDataOrRecordType)
import Agda.TypeChecking.Errors (dropTopLevelModule)
import Agda.TypeChecking.Irrelevance
-- Prevent "Ambiguous occurrence ‘DontKnow’" when loading with ghci.
-- (DontKnow is one of the constructors of ErrorNonEmpty *and* UnifactionResult').
-- We can't explicitly hide just the constructor here because it isn't in the
-- hs-boot file.
import {-# SOURCE #-} Agda.TypeChecking.Empty (ensureEmptyType)
import Agda.TypeChecking.Patterns.Abstract
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Records hiding (getRecordConstructor)
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Sort
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope
import Agda.TypeChecking.Telescope.Path
import Agda.TypeChecking.Primitive hiding (Nat)
import Agda.TypeChecking.Warnings (warning)

import {-# SOURCE #-} Agda.TypeChecking.Rules.Term (checkExpr, isType_)
import Agda.TypeChecking.Rules.LHS.Problem
import Agda.TypeChecking.Rules.LHS.ProblemRest
import Agda.TypeChecking.Rules.LHS.Unify
import Agda.TypeChecking.Rules.LHS.Implicit

import Agda.Utils.CallStack ( HasCallStack, withCallerCallStack )
import Agda.Utils.Function
import Agda.Utils.Functor
import Agda.Utils.Lens
import Agda.Utils.List
import Agda.Utils.List1 (List1, pattern (:|))
import Agda.Utils.List2 (pattern List2)
import qualified Agda.Utils.List1 as List1
import qualified Agda.Utils.List2 as List2
import Agda.Utils.Maybe
import Agda.Utils.Monad
import Agda.Utils.Null
import qualified Agda.Syntax.Common.Pretty as P
import Agda.Syntax.Common.Pretty (prettyShow)
import Agda.Utils.Singleton
import Agda.Utils.Size
import Agda.Utils.Tuple

import Agda.Utils.Impossible
import Agda.TypeChecking.Free (freeIn)

-- | Extra read-only state for the LHS checker.
--
data LHSContext = LHSContext
  { lhsRange       :: Range  -- ^ The range of the whole lhs of a clause.
  , lhsContextSize :: Nat    -- ^ Original size of the context in which the lhs checker runs.
  }

-- | A pattern is flexible if it is dotted or implicit, or a record pattern
--   with only flexible subpatterns.
class IsFlexiblePattern a where
  maybeFlexiblePattern :: (HasConstInfo m, MonadDebug m) => a -> MaybeT m FlexibleVarKind

  isFlexiblePattern :: (HasConstInfo m, MonadDebug m) => a -> m Bool
  isFlexiblePattern p =
    maybe False notOtherFlex <$> runMaybeT (maybeFlexiblePattern p)
    where
    notOtherFlex = \case
      RecordFlex fls -> all notOtherFlex fls
      ImplicitFlex   -> True
      DotFlex        -> True
      OtherFlex      -> False

instance IsFlexiblePattern A.Pattern where
  maybeFlexiblePattern p = do
    reportSDoc "tc.lhs.flex" 30 $ "maybeFlexiblePattern" <+> prettyA p
    reportSDoc "tc.lhs.flex" 60 $ "maybeFlexiblePattern (raw) " <+> (text . show . deepUnscope) p
    case p of
      A.DotP{}  -> return DotFlex
      A.VarP{}  -> return ImplicitFlex
      A.WildP{} -> return ImplicitFlex
      A.AsP _ _ p -> maybeFlexiblePattern p
      A.ConP _ cs qs | Just c <- getUnambiguous cs ->
        ifM (isNothing <$> isRecordConstructor c) (return OtherFlex) {-else-}
            (maybeFlexiblePattern qs)
      A.LitP{}  -> return OtherFlex
      _ -> mzero

instance IsFlexiblePattern (I.Pattern' a) where
  maybeFlexiblePattern p =
    case p of
      I.DotP{}  -> return DotFlex
      I.ConP _ i ps
        | conPRecord i , PatOSystem <- patOrigin (conPInfo i) -> return ImplicitFlex  -- expanded from ImplicitP
        | conPRecord i -> maybeFlexiblePattern ps
        | otherwise -> mzero
      I.VarP{}  -> mzero
      I.LitP{}  -> mzero
      I.ProjP{} -> mzero
      I.IApplyP{} -> mzero
      I.DefP{} -> mzero -- TODO Andrea check semantics

-- | Lists of flexible patterns are 'RecordFlex'.
instance IsFlexiblePattern a => IsFlexiblePattern [a] where
  maybeFlexiblePattern ps = RecordFlex <$> mapM maybeFlexiblePattern ps

instance IsFlexiblePattern a => IsFlexiblePattern (Arg a) where
  maybeFlexiblePattern = maybeFlexiblePattern . unArg

instance IsFlexiblePattern a => IsFlexiblePattern (Common.Named name a) where
  maybeFlexiblePattern = maybeFlexiblePattern . namedThing

-- | Update the given LHS state:
--   1. simplify problem equations
--   2. rename telescope variables
--   3. introduce trailing patterns
updateLHSState :: LHSState a -> TCM (LHSState a)
updateLHSState st = do
  let tel     = st ^. lhsTel
      problem = st ^. lhsProblem
  eqs' <- addContext tel $ updateProblemEqs $ problem ^. problemEqs
  tel' <- useNamesFromProblemEqs eqs' tel
  updateProblemRest $ set lhsTel tel' $ set (lhsProblem . problemEqs) eqs' st

-- | Update the user patterns in the given problem, simplifying equations
--   between constructors where possible.
updateProblemEqs
 :: [ProblemEq] -> TCM [ProblemEq]
updateProblemEqs eqs = do
  reportSDoc "tc.lhs.top" 20 $ vcat
    [ "updateProblem: equations to update"
    , nest 2 $ if null eqs then "(none)" else vcat $ map prettyTCM eqs
    ]

  eqs' <- updates eqs

  reportSDoc "tc.lhs.top" 20 $ vcat
    [ "updateProblem: new equations"
    , nest 2 $ if null eqs' then "(none)" else vcat $ map prettyTCM eqs'
    ]

  return eqs'

  where

    updates :: [ProblemEq] -> TCM [ProblemEq]
    updates = concat <.> traverse update

    update :: ProblemEq -> TCM [ProblemEq]
    update eq@(ProblemEq A.WildP{} _ _) = return []
    update eq@(ProblemEq p@A.ProjP{} _ _) = typeError $ IllformedProjectionPatternAbstract p
    update eq@(ProblemEq p@(A.AsP info x p') v a) =
      (ProblemEq (A.VarP x) v a :) <$> update (ProblemEq p' v a)

    update eq@(ProblemEq p v a) = reduce v >>= constructorForm >>= \case
      Con c ci es -> do
        let vs = fromMaybe __IMPOSSIBLE__ $ allApplyElims es
        -- we should only simplify equations between fully applied constructors
        contype <- getFullyAppliedConType c =<< reduce (unDom a)
        caseMaybe contype (return [eq]) $ \((d,_,pars),b) -> do
        TelV ctel _ <- telViewPath b

        -- Andrea 15/10/2020: propagate modality to constructor arguments
        let updMod = composeModality (getModality a)
        ctel <- return $ mapModality updMod <$> ctel

        let bs = instTel ctel (map unArg vs)

        p <- expandLitPattern p
        case p of
          A.AsP{} -> __IMPOSSIBLE__
          A.ConP cpi ambC ps -> do
            (c',_) <- disambiguateConstructor ambC d pars

            -- Issue #3014: If the constructor is forced but the user wrote a
            -- different constructor,that's an error. We simply keep the
            -- problem equation, this will result in a proper error message later.
            if conName c /= conName c' then return [eq] else do

            -- Insert implicit patterns
            ps <- insertImplicitPatterns ExpandLast ps ctel
            reportSDoc "tc.lhs.imp" 20 $
              "insertImplicitPatternsT returned" <+> fsep (map prettyA ps)

            -- Check argument count and hiding (not just count: #3074)
            let checkArgs [] [] _ _ = return ()
                checkArgs (p : ps) (v : vs) nExpected nActual
                  | getHiding p == getHiding v = checkArgs ps vs (nExpected + 1) (nActual + 1)
                  | otherwise                  = setCurrentRange p $ typeError WrongHidingInLHS
                checkArgs [] vs nExpected nActual = typeError $
                  WrongNumberOfConstructorArguments (conName c) (nExpected + length vs) nActual
                checkArgs (p : ps) [] nExpected nActual = setCurrentRange p $ typeError $
                  WrongNumberOfConstructorArguments (conName c) nExpected (nActual + 1 + (length ps))

            checkArgs ps vs 0 0

            updates $ zipWith3 ProblemEq (map namedArg ps) (map unArg vs) bs

          A.RecP pi fs -> do
            axs <- map argFromDom . recFields . theDef <$> getConstInfo d

            -- Andreas, 2018-09-06, issue #3122.
            -- Associate the concrete record field names used in the record pattern
            -- to their counterpart in the record type definition.
            disambiguateRecordFields (map _nameFieldA fs) (map unArg axs)

            let cxs = map (fmap (nameConcrete . qnameName)) axs

            -- In fs omitted explicit fields are replaced by underscores,
            -- and the fields are put in the correct order.
            ps <- insertMissingFieldsFail A.RecStyleBrace d (const $ A.WildP empty) fs cxs

            -- We also need to insert missing implicit or instance fields.
            ps <- insertImplicitPatterns ExpandLast ps ctel

            let eqs = zipWith3 ProblemEq (map namedArg ps) (map unArg vs) bs
            updates eqs

          _ -> return [eq]

      Lit l | A.LitP _ l' <- p , l == l' -> return []

      _ | A.EqualP{} <- p -> do
        itisone <- liftTCM primItIsOne
        ifM (tryConversion $ equalTerm (unDom a) v itisone) (return []) (return [eq])

      _ -> return [eq]

    instTel :: Telescope -> [Term] -> [Dom Type]
    instTel EmptyTel _                   = []
    instTel (ExtendTel arg tel) (u : us) = arg : instTel (absApp tel u) us
    instTel ExtendTel{} []               = __IMPOSSIBLE__


-- | Check if a problem is solved.
--   That is, if the patterns are all variables,
--   and there is no 'problemRest'.
isSolvedProblem :: Problem a -> Bool
isSolvedProblem problem = null (problem ^. problemRestPats) &&
  problemAllVariables problem

-- | Check if a problem consists only of variable patterns.
--   (Includes the 'problemRest').
problemAllVariables :: Problem a -> Bool
problemAllVariables problem =
    all isSolved $
      map namedArg (problem ^. problemRestPats) ++ problemInPats problem
  where
    -- need further splitting:
    isSolved A.ConP{}        = False
    isSolved A.LitP{}        = False
    isSolved A.RecP{}        = False  -- record pattern
    -- solved:
    isSolved A.VarP{}        = True
    isSolved A.WildP{}       = True
    isSolved A.DotP{}        = True
    isSolved A.AbsurdP{}     = True
    -- recursive cases
    isSolved (A.AsP _ _ p)   = isSolved p
    -- impossible:
    isSolved A.ProjP{}       = __IMPOSSIBLE__
    isSolved A.DefP{}        = __IMPOSSIBLE__
    isSolved A.PatternSynP{} = __IMPOSSIBLE__  -- expanded before
    isSolved A.EqualP{}      = False -- __IMPOSSIBLE__
    isSolved A.WithP{}       = __IMPOSSIBLE__

-- | For each user-defined pattern variable in the 'Problem', check
-- that the corresponding data type (if any) does not contain a
-- constructor of the same name (which is not in scope); this
-- \"shadowing\" could indicate an error, and is not allowed.
--
-- Precondition: The problem has to be solved.

noShadowingOfConstructors :: ProblemEq -> TCM ()
noShadowingOfConstructors problem@(ProblemEq p _ (Dom{domInfo = info, unDom = El _ a})) =
  case p of
   A.WildP       {} -> return ()
   A.AbsurdP     {} -> return ()
   A.DotP        {} -> return ()
   A.EqualP      {} -> return ()
   A.AsP _ _ p      -> noShadowingOfConstructors $ problem { problemInPat = p }
   A.ConP        {} -> __IMPOSSIBLE__
   A.RecP        {} -> __IMPOSSIBLE__
   A.ProjP       {} -> __IMPOSSIBLE__
   A.DefP        {} -> __IMPOSSIBLE__
   A.LitP        {} -> __IMPOSSIBLE__
   A.PatternSynP {} -> __IMPOSSIBLE__
   A.WithP       {} -> __IMPOSSIBLE__
   -- Andreas, 2017-12-01, issue #2859.
   -- Due to parameter refinement, there can be (invisible) variable patterns from module
   -- parameters that shadow constructors.
   -- Thus, only complain about user written variable that shadow constructors.
   A.VarP A.BindName{unBind = x} -> when (getOrigin info == UserWritten) $ do
    reportSDoc "tc.lhs.shadow" 30 $ vcat
      [ text $ "checking whether pattern variable " ++ prettyShow x ++ " shadows a constructor"
      , nest 2 $ "type of variable =" <+> prettyTCM a
      , nest 2 $ "position of variable =" <+> (text . show) (getRange x)
      ]
    reportSDoc "tc.lhs.shadow" 70 $ nest 2 $ "a =" <+> pretty a

    -- Get a conflicting data or record constructor, if any.
    mc <- runMaybeT do

      -- Is the type of the pattern variable a data or pattern record type?
      a  <- lift $ reduce a
      (d, dr) <- MaybeT $ isDataOrRecord a
      guard $ patternMatchingAllowed dr

      -- Look for a constructor with the same name as the pattern variable.
      cs <- lift $ getConstructors d
      MaybeT $ pure $ List.find ((A.nameConcrete x ==) . A.nameConcrete . A.qnameName) cs

    -- Alert if there is a constructor of the same name.
    whenJust mc \ c -> setCurrentRange x $
      warning $ PatternShadowsConstructor (nameConcrete x) c
    --
    -- Andreas, 2023-09-08, issue #6829:
    -- I rewrote the code originally dating from 2009, commit:
    -- https://github.com/agda/agda/commit/5d5095ba080b04f16867d4ed5af4ba7091f1a773
    -- The code survived for almost 15 years, but it slept through the advent
    -- of matchable record constructors in 2010 (Agda 2.2.8):
    -- https://github.com/agda/agda/blob/283730b392d7c21c54b53b0f486802ec143e4af7/doc/release-notes/2.2.8.md#L7-L9
    -- Here are comments on the last version of the code I'd like to preserve,
    -- as they reflect some considerations and design decisions:
    --
            -- Abstract constructors cannot be brought into scope,
            -- even by a bigger import list.
            -- Thus, they cannot be confused with variables.
            -- Alternatively, we could do getConstInfo in ignoreAbstractMode,
            -- then Agda would complain if a variable shadowed an abstract constructor.
          -- TODO: in the future some stuck primitives might allow constructors
      -- TODO: If the type is a meta-variable, should the test be
      -- postponed? If there is a problem, then it will be caught when
      -- the completed module is type checked, so it is safe to skip
      -- the test here. However, users may be annoyed if they get an
      -- error in code which has already passed the type checker.

-- | Check that a dot pattern matches it's instantiation.
checkDotPattern :: DotPattern -> TCM ()
checkDotPattern (Dot e v (Dom{domInfo = info, unDom = a})) =
  traceCall (CheckDotPattern e v) $ do
  reportSDoc "tc.lhs.dot" 15 $
    sep [ "checking dot pattern"
        , nest 2 $ prettyA e
        , nest 2 $ "=" <+> prettyTCM v
        , nest 2 $ ":" <+> prettyTCM a
        ]
  applyModalityToContext info $ do
    u <- checkExpr e a
    reportSDoc "tc.lhs.dot" 50 $
      sep [ "equalTerm"
          , nest 2 $ pretty a
          , nest 2 $ pretty u
          , nest 2 $ pretty v
          ]
    equalTerm a u v

checkAbsurdPattern :: AbsurdPattern -> TCM ()
checkAbsurdPattern (Absurd r a) = ensureEmptyType r a

checkAnnotationPattern :: AnnotationPattern -> TCM ()
checkAnnotationPattern (Ann t a) = do
  reportSDoc "tc.lhs.ann" 15 $
    sep [ "checking type annotation in pattern"
        , nest 2 $ prettyA t
        , nest 2 $ "=" <+> prettyTCM a
        ]
  b <- isType_ t
  equalType a b

-- | After splitting is complete, we transfer the origins
--   We also transfer the locations of absurd patterns, since these haven't
--   been introduced yet in the internal pattern.
transferOrigins :: [NamedArg A.Pattern]
                -> [NamedArg DeBruijnPattern]
                -> TCM [NamedArg DeBruijnPattern]
transferOrigins ps qs = do
  reportSDoc "tc.lhs.origin" 40 $ vcat
    [ "transferOrigins"
    , nest 2 $ vcat
      [ "ps  =   " <+> prettyA ps
      , "qs  =   " <+> pretty qs
      ]
    ]
  transfers ps qs

  where
    transfers :: [NamedArg A.Pattern]
              -> [NamedArg DeBruijnPattern]
              -> TCM [NamedArg DeBruijnPattern]
    transfers [] qs
      | all notVisible qs = return $ map (setOrigin Inserted) qs
      | otherwise         = __IMPOSSIBLE__
    transfers (p : ps) [] = __IMPOSSIBLE__
    transfers (p : ps) (q : qs)
      | matchingArgs p q = do
          q' <- mapNameOf (maybe id (const . Just) $ getNameOf p) -- take NamedName from p if present
              . setOrigin (getOrigin p)
            <$> (traverse $ traverse $ transfer $ namedArg p) q
          (q' :) <$> transfers ps qs
      | otherwise = (setOrigin Inserted q :) <$> transfers (p : ps) qs

    transfer :: A.Pattern -> DeBruijnPattern -> TCM DeBruijnPattern
    transfer p q = case (asView p , q) of

      ((asB , A.ConP pi _ ps) , ConP c (ConPatternInfo i r ft mb l) qs) -> do
        let cpi = ConPatternInfo (PatternInfo PatOCon asB) r ft mb l
        ConP c cpi <$> transfers ps qs

      ((asB , A.RecP pi fs) , ConP c (ConPatternInfo i r ft mb l) qs) -> do
        let Def d _  = unEl $ unArg $ fromMaybe __IMPOSSIBLE__ mb
            axs = map (nameConcrete . qnameName . unArg) (conFields c) `withArgsFrom` qs
            cpi = ConPatternInfo (PatternInfo PatORec asB) r ft mb l
        ps <- insertMissingFieldsFail A.RecStyleBrace d (const $ A.WildP empty) fs axs
        ConP c cpi <$> transfers ps qs

      ((asB , p) , ConP c (ConPatternInfo i r ft mb l) qs) -> do
        let cpi = ConPatternInfo (PatternInfo (patOrig p) asB) r ft mb l
        return $ ConP c cpi qs

      ((asB , p) , VarP _ x) -> return $ VarP (PatternInfo (patOrig p) asB) x

      ((asB , p) , DotP _ u) -> return $ DotP (PatternInfo (patOrig p) asB) u

      ((asB , p) , LitP _ l) -> return $ LitP (PatternInfo (patOrig p) asB) l

      _ -> return q

    patOrig :: A.Pattern -> PatOrigin
    patOrig (A.VarP x)      = PatOVar (A.unBind x)
    patOrig A.DotP{}        = PatODot
    patOrig A.ConP{}        = PatOCon
    patOrig A.RecP{}        = PatORec
    patOrig A.WildP{}       = PatOWild
    patOrig A.AbsurdP{}     = PatOAbsurd
    patOrig A.LitP{}        = PatOLit
    patOrig A.EqualP{}      = PatOCon --TODO: origin for EqualP
    patOrig A.AsP{}         = __IMPOSSIBLE__
    patOrig A.ProjP{}       = __IMPOSSIBLE__
    patOrig A.DefP{}        = __IMPOSSIBLE__
    patOrig A.PatternSynP{} = __IMPOSSIBLE__
    patOrig A.WithP{}       = __IMPOSSIBLE__

    matchingArgs :: NamedArg A.Pattern -> NamedArg DeBruijnPattern -> Bool
    matchingArgs p q
      -- The arguments match if
      -- 1. they are both projections,
      | isJust (A.isProjP p) = isJust (isProjP q)
      -- 2. or they are both visible,
      | visible p && visible q = True
      -- 3. or they have the same hiding and the argument is not named,
      | sameHiding p q && isNothing (getNameOf p) = True
      -- 4. or they have the same hiding and the same name.
      | sameHiding p q && namedSame p q = True
      -- Otherwise this argument was inserted by the typechecker.
      | otherwise = False


-- | If a user-written variable occurs more than once, it should be bound
--   to the same internal variable (or term) in all positions.
--   Returns the list of patterns with the duplicate user patterns removed.
checkPatternLinearity :: [ProblemEq] -> TCM [ProblemEq]
checkPatternLinearity eqs = do
  reportSDoc "tc.lhs.linear" 30 $ "Checking linearity of pattern variables"
  check Map.empty eqs
  where
    check :: Map A.BindName (Term, Type) -> [ProblemEq] -> TCM [ProblemEq]
    check _ [] = return []
    check vars (eq@(ProblemEq p u a) : eqs) = do
      reportSDoc "tc.lhs.linear" 40 $ sep
        [ "linearity: checking pattern "
        , prettyA p
        , " equal to term "
        , prettyTCM u
        , " of type "
        , prettyTCM a
        ]
      case p of
        A.VarP x -> do
          let y = A.unBind x
          reportSLn "tc.lhs.linear" 60 $
            "pattern variable " ++ prettyShow (A.nameConcrete y) ++ " with id " ++ show (A.nameId y)
          case Map.lookup x vars of
            Just (v , b) -> do
              traceCall (CheckPatternLinearityType $ A.nameConcrete y) $
                noConstraints $ equalType (unDom a) b
              traceCall (CheckPatternLinearityValue $ A.nameConcrete y) $
                noConstraints $ equalTerm (unDom a) u v
              check vars eqs
            Nothing -> (eq:) <$> do
              check (Map.insert x (u,unDom a) vars) eqs
        A.AsP _ x p ->
          check vars $ [ProblemEq (A.VarP x) u a, ProblemEq p u a] ++ eqs
        A.WildP{}       -> continue
        A.DotP{}        -> continue
        A.AbsurdP{}     -> continue
        A.ConP{}        -> __IMPOSSIBLE__
        A.ProjP{}       -> __IMPOSSIBLE__
        A.DefP{}        -> __IMPOSSIBLE__
        A.LitP{}        -> __IMPOSSIBLE__
        A.PatternSynP{} -> __IMPOSSIBLE__
        A.RecP{}        -> __IMPOSSIBLE__
        A.EqualP{}      -> __IMPOSSIBLE__
        A.WithP{}       -> __IMPOSSIBLE__

      where continue = (eq:) <$> check vars eqs

-- | Construct the context for a left hand side, making up out-of-scope names
--   for unnamed variables.
computeLHSContext :: [Maybe A.Name] -> Telescope -> TCM Context
computeLHSContext = go [] []
  where
    go cxt _ []        tel@ExtendTel{} = do
      reportSDoc "impossible" 10 $
        "computeLHSContext: no patterns left, but tel =" <+> prettyTCM tel
      __IMPOSSIBLE__
    go cxt _ (_ : _)   EmptyTel = __IMPOSSIBLE__
    go cxt _ []        EmptyTel = return cxt
    go cxt taken (x : xs) tel0@(ExtendTel a tel) = do
        name <- maybe (dummyName taken $ absName tel) return x
        let e = (name,) <$> a
        go (e : cxt) (name : taken) xs (absBody tel)

    dummyName taken s =
      if isUnderscore s then freshNoName_
      else setNotInScope <$> freshName_ (argNameToString s)

-- | Bind as patterns
bindAsPatterns :: [AsBinding] -> TCM a -> TCM a
bindAsPatterns []                ret = ret
bindAsPatterns (AsB x v a m : asb) ret = do
  reportSDoc "tc.lhs.as" 10 $ "as pattern" <+> prettyTCM x <+>
    sep [ ":" <+> prettyTCM a
        , "=" <+> prettyTCM v
        ]
  addLetBinding (setModality m defaultArgInfo) Inserted x v a $ bindAsPatterns asb ret

-- | Since with-abstraction can change the type of a variable, we have to
--   recheck the stripped with patterns when checking a with function.
recheckStrippedWithPattern :: ProblemEq -> TCM ()
recheckStrippedWithPattern (ProblemEq p v a) = checkInternal v CmpLeq (unDom a)
  `catchError` \_ -> typeError $ IllTypedPatternAfterWithAbstraction p

-- | Result of checking the LHS of a clause.
data LHSResult = LHSResult
  { lhsParameters   :: Nat
    -- ^ The number of original module parameters. These are present in the
    -- the patterns.
  , lhsVarTele      :: Telescope
    -- ^ Δ : The types of the pattern variables, in internal dependency order.
    -- Corresponds to 'clauseTel'.
  , lhsPatterns     :: [NamedArg DeBruijnPattern]
    -- ^ The patterns in internal syntax.
  , lhsHasAbsurd    :: Bool
    -- ^ Whether the LHS has at least one absurd pattern.
  , lhsBodyType     :: Arg Type
    -- ^ The type of the body. Is @bσ@ if @Γ@ is defined.
    -- 'Irrelevant' to indicate the rhs must be checked in irrelevant mode.
  , lhsPatSubst     :: Substitution
    -- ^ Substitution version of @lhsPatterns@, only up to the first projection
    -- pattern. @Δ |- lhsPatSubst : Γ@. Where @Γ@ is the argument telescope of
    -- the function. This is used to update inherited dot patterns in
    -- with-function clauses.
  , lhsAsBindings   :: [AsBinding]
    -- ^ As-bindings from the left-hand side. Return instead of bound since we
    -- want them in where's and right-hand sides, but not in with-clauses
    -- (Issue 2303).
  , lhsPartialSplit :: IntSet
    -- ^ have we done a partial split?
  , lhsIndexedSplit :: Bool
    -- ^ have we split on an indexed type?
  }

instance InstantiateFull LHSResult where
  instantiateFull' (LHSResult n tel ps abs t sub as psplit ixsplit) = LHSResult n
    <$> instantiateFull' tel
    <*> instantiateFull' ps
    <*> instantiateFull' abs
    <*> instantiateFull' t
    <*> instantiateFull' sub
    <*> instantiateFull' as
    <*> pure psplit
    <*> pure ixsplit

-- | Check a LHS. Main function.
--
--   @checkLeftHandSide a ps a ret@ checks that user patterns @ps@ eliminate
--   the type @a@ of the defined function, and calls continuation @ret@
--   if successful.

checkLeftHandSide :: forall a.
     Call
     -- ^ Trace, e.g. 'CheckLHS' or 'CheckPattern'.
  -> Range
     -- ^ 'Range' of the entire left hand side, for error reporting.
  -> Maybe QName
     -- ^ The name of the definition we are checking.
  -> [NamedArg A.Pattern]
     -- ^ The patterns.
  -> Type
     -- ^ The expected type @a = Γ → b@.
  -> Maybe Substitution
     -- ^ Module parameter substitution from with-abstraction.
  -> [ProblemEq]
     -- ^ Patterns that have been stripped away by with-desugaring.
     -- ^ These should not contain any proper matches.
  -> (LHSResult -> TCM a)
     -- ^ Continuation.
  -> TCM a
checkLeftHandSide call lhsRng f ps a withSub' strippedPats =
 Bench.billToCPS [Bench.Typing, Bench.CheckLHS] $
 traceCallCPS call $ \ ret -> do

  -- To allow module parameters to be refined by matching, we're adding the
  -- context arguments as wildcard patterns and extending the type with the
  -- context telescope.
  cxt <- map (setOrigin Inserted) . reverse <$> getContext
  let tel = telFromList' prettyShow cxt
      cps = [ unnamed . A.VarP . A.mkBindName . fst <$> argFromDom d
            | d <- cxt ]
      eqs0 = zipWith3 ProblemEq (map namedArg cps) (map var $ downFrom $ size tel) (flattenTel tel)

  let finalChecks :: LHSState a -> TCM a
      finalChecks (LHSState delta qs0 (Problem eqs rps _) b psplit ixsplit) = do

        reportSDoc "tc.lhs.top" 20 $ vcat
          [ "lhs: final checks with remaining equations"
          , nest 2 $ if null eqs then "(none)" else addContext delta $ vcat $ map prettyTCM eqs
          , "qs0 =" <+> addContext delta (prettyTCMPatternList qs0)
          ]

        unless (null rps) __IMPOSSIBLE__

        addContext delta $ do
          mapM_ noShadowingOfConstructors eqs

          -- When working --without-K or --cubical-compatible, we have
          -- to check that the target type can be used at the “ambient”
          -- modality. For --cubical-compatible, this just improves an
          -- error message (printing the type rather than the generated
          -- RHS). For --without-K, it implements the same check without
          -- necessarily generating --cubical code.
          -- The reason for this check is that a clause
          --    foo : x ≡ y → ... → T y
          --    foo refl ... = ...
          -- in Cubical mode, gets elaborated to an extra clause of the
          -- form
          --    foo (transp p φ x) ... = transp (λ i → T (p i)) φ (foo x ...)
          -- (approximately), where T is the target type. That is: to
          -- implement the substitution T[y/x], we use an actual
          -- transport. See #5448.

        arity_a <- arityPiPath a
        -- Compute substitution from the out patterns @qs0@
        let notProj ProjP{} = False
            notProj _       = True
            numPats  = length $ takeWhile (notProj . namedArg) qs0

            -- We have two slightly different cases here: normal function and
            -- with-function. In both cases the goal is to build a substitution
            -- from the context Γ of the previous checkpoint to the current lhs
            -- context Δ:
            --
            --    Δ ⊢ paramSub : Γ
            --
            --  * Normal function, f
            --
            --    Γ = cxt = module parameter telescope of f
            --    Ψ = non-parameter arguments of f (we have f : Γ Ψ → A)
            --    Δ   ⊢ patSub  : Γ Ψ
            --    Γ Ψ ⊢ weakSub : Γ
            --    paramSub = patSub ∘ weakSub
            --
            --  * With-function
            --
            --    Γ = lhs context of the parent clause (cxt = [])
            --    Ψ = argument telescope of with-function
            --    Θ = inserted implicit patterns not in Ψ (#2827)
            --        (this happens if the goal computes to an implicit
            --         function type after some matching in the with-clause)
            --
            --    Ψ   ⊢ withSub : Γ
            --    Δ   ⊢ patSub  : Ψ Θ
            --    Ψ Θ ⊢ weakSub : Ψ
            --    paramSub = patSub ∘ weakSub ∘ withSub
            --
            --    To compute Θ we can look at the arity of the with-function
            --    and compare it to numPats. This works since the with-function
            --    type is fully reduced.

            weakSub :: Substitution
            weakSub | isJust withSub' = wkS (max 0 $ numPats - arity_a) idS -- if numPats < arity, Θ is empty
                    | otherwise       = wkS (numPats - length cxt) idS
            withSub  = fromMaybe idS withSub'
            patSub   = map (patternToTerm . namedArg) (reverse $ take numPats qs0) ++# EmptyS impossible
            paramSub = patSub `composeS` weakSub `composeS` withSub

        eqs <- addContext delta $ checkPatternLinearity eqs

        leftovers@(LeftoverPatterns patVars asb0 dots absurds annps otherPats)
          <- addContext delta $ getLeftoverPatterns eqs

        reportSDoc "tc.lhs.leftover" 30 $ vcat
          [ "leftover patterns: " , nest 2 (addContext delta $ prettyTCM leftovers) ]

        unless (null otherPats) __IMPOSSIBLE__

        -- Get the user-written names for the pattern variables
        let (vars, asb1) = getUserVariableNames delta patVars
            asb          = asb0 ++ asb1

        -- Rename internal patterns with these names
        let makeVar     = maybe deBruijnVar $ debruijnNamedVar . nameToArgName
            ren         = parallelS $ zipWith makeVar (reverse vars) [0..]

        qs <- transferOrigins (cps ++ ps) $ applySubst ren qs0

        let hasAbsurd = not . null $ absurds

        let lhsResult = LHSResult (length cxt) delta qs hasAbsurd b patSub asb (IntSet.fromList $ catMaybes psplit) ixsplit

        -- Debug output
        reportSDoc "tc.lhs.top" 10 $
          vcat [ "checked lhs:"
               , nest 2 $ vcat
                 [ "delta   = " <+> prettyTCM delta
                 , "dots    = " <+> addContext delta (brackets $ fsep $ punctuate comma $ map prettyTCM dots)
                 , "asb     = " <+> addContext delta (brackets $ fsep $ punctuate comma $ map prettyTCM asb)
                 , "absurds = " <+> addContext delta (brackets $ fsep $ punctuate comma $ map prettyTCM absurds)
                 , "qs      = " <+> addContext delta (prettyList $ map pretty qs)
                 , "b       = " <+> addContext delta (prettyTCM b)
                 ]
               ]
        reportSDoc "tc.lhs.top" 30 $
          nest 2 $ vcat
                 [ "vars   = " <+> pretty vars
                 , "b      = " <+> pretty b
                 ]
        reportSDoc "tc.lhs.top" 20 $ nest 2 $ "withSub  = " <+> pretty withSub
        reportSDoc "tc.lhs.top" 20 $ nest 2 $ "weakSub  = " <+> pretty weakSub
        reportSDoc "tc.lhs.top" 20 $ nest 2 $ "patSub   = " <+> pretty patSub
        reportSDoc "tc.lhs.top" 20 $ nest 2 $ "paramSub = " <+> pretty paramSub

        newCxt <- computeLHSContext vars delta

        updateContext paramSub (const newCxt) $ do

          reportSDoc "tc.lhs.top" 10 $ "bound pattern variables"
          reportSDoc "tc.lhs.top" 60 $ nest 2 $ "context = " <+> (pretty =<< getContextTelescope)
          reportSDoc "tc.lhs.top" 10 $ nest 2 $ "type  = " <+> prettyTCM b
          reportSDoc "tc.lhs.top" 60 $ nest 2 $ "type  = " <+> pretty b

          bindAsPatterns asb $ do

            -- Check dot patterns
            mapM_ checkDotPattern dots
            mapM_ checkAbsurdPattern absurds
            mapM_ checkAnnotationPattern annps

          -- Issue2303: don't bind asb' for the continuation (return in lhsResult instead)
          ret lhsResult

  st0 <- initLHSState tel eqs0 ps a finalChecks

  -- after we have introduced variables, we can add the patterns stripped by
  -- with-desugaring to the state.
  let withSub = fromMaybe __IMPOSSIBLE__ withSub'
  withEqs <- updateProblemEqs $ applySubst withSub strippedPats
  -- Jesper, 2017-05-13: re-check the stripped patterns here!
  inTopContext $ addContext (st0 ^. lhsTel) $
    forM_ withEqs recheckStrippedWithPattern

  let st = over (lhsProblem . problemEqs) (++ withEqs) st0

  -- doing the splits:
  let initLHSContext = LHSContext { lhsRange = lhsRng, lhsContextSize = size cxt }
  (result, block) <- unsafeInTopContext $ runWriterT $ (`runReaderT` initLHSContext) $ checkLHS f st
  return result

-- | Check that this split will generate a modality-correct internal
-- clause when --cubical-compatible is used. This means that the type of
-- anything which might be transported must be modality-correct. This is
-- necessarily an approximate check. We assume that any argument which
-- (a) comes after and (b) mentions a dotted argument will be
-- transported, which is probably an overestimate.
conSplitModalityCheck ::
     Range
       -- ^ Range of the whole left hand side, for error reporting.
  -> Modality
       -- ^ Modality to check at.
  -> PatternSubstitution
      -- ^ Substitution resulting from index unification. @Γ ⊢ ρ : Δ'@,
      -- where @Δ'@ is the context we're in, and @Γ@ is the clause telescope
      -- before unification.
  -> Int       -- ^ Variable @x@ at which we split.
  -> Telescope -- ^ The telescope @Γ@ itself.
  -> Type      -- ^ Target type of the clause.
  -> TCM ()
conSplitModalityCheck lhsRng mod rho blocking gamma target = when (any ((/= defaultModality) . getModality) gamma) $ do
  reportSDoc "tc.lhs.top" 30 $ vcat
    [ "LHS modality check for modality: " <+> prettyTCM mod
    , "rho:    " <+> inTopContext (prettyTCM rho)
    , "gamma:  " <+> inTopContext (prettyTCM gamma)
    , "target: " <+> prettyTCM target
    , "target (raw): " <+> pretty target
    , "Δ'target: " <+> prettyTCM (applyPatSubst rho target)
    , "blocking:" <+> prettyTCM blocking
    ]
  whenJust (firstForced rho (length gamma)) \ ix -> do
      -- We've found a forced argument. This means that the unifier has
      -- decided to kill a unification variable, and any of its
      -- occurrences in the generated term will be replaced by an
      -- occurrence of a path, and any terms whose types mention that
      -- variable will be transported.
      let
        (gamma0, delta) = splitTelescopeAt (length gamma - ix) gamma
        name = inTopContext . addContext gamma . nameOfBV
        delta'target = applyPatSubst rho target
      reportSDoc "tc.lhs.top" 30 $ vcat
        [ "found forced argument!"
        , "forced: " <+> prettyTCM ix
        , "before: " <+> inTopContext (prettyTCM gamma0)
        , "after:  " <+> inTopContext (addContext gamma0 (prettyTCM delta))
        ]
      forced <- name ix
      forM_ (zip [ix - 1, ix - 2 ..] (telToList delta)) $ \(arg, d) -> do
        -- Example: The first argument after the first forced variable. So
        -- we have e.g.:
        --   Γ = Γ₀.x.Δ
        --   Δ' ⊢ ρ : Γ₀.x.Δ
        --   Γ₀ ⊢ x : Type
        -- but we need
        --   Δ' ⊢ x : Type,
        -- since Δ' is the context we are in. Then we have
        --   Γ ⊢ x[wkS |Δ|] : Type
        -- and consequently
        --   Δ' ⊢ x[wkS |Δ|][ρ] : Type
        let
          rho' = composeS rho (wkS (arg + 1) idS)
        ty' <- reduce (applyPatSubst rho' (unEl (snd (unDom d))))
        let
          -- It's actually rather tricky to know when, exactly, a
          -- transport will be needed in a position that forces an
          -- usable-at-modality check. Our current heuristic is:
          --
          -- The variable we're looking at has a fibrant type, with the
          -- first forced variable free.
          -- The variable appears free in the result type.
          docheck = and
            [ ix `freeIn` applySubst (wkS (arg + 1) idS) (unEl (snd (unDom d)))
            , arg /= blocking
            , arg `freeIn` target
            ]
        reportSDoc "tc.lhs.top" 30 $ vcat
          [ "arg:        " <+> pretty arg
          , "arg type:   " <+> prettyTCM (applySubst (wkS (arg + 1) idS) (unEl (snd (unDom d))))
          , "check       " <+> pretty docheck
          ]
        argn <- name arg
        when docheck $
          usableAtModality (IndexedClauseArg forced argn) mod ty'

  -- ALways check the target clause type. Specifically, we check it both
  -- in Δ' and in Γ. The check in Δ' will sometimes let slip by a
  -- quantity violation which is masked by an indexed match (recall that
  -- the unifier likes to replace @0-variables for @ω-variables). A
  -- concrete case where this happens is #5468. Check in Δ' first since
  -- that will have the forced variable names.
  setCurrentRange lhsRng do
    usableAtModality IndexedClause mod (unEl (applyPatSubst rho target))
    inTopContext $ addContext gamma $ usableAtModality IndexedClause mod (unEl target)
  where
    -- Find the first dotted pattern in the substitution. "First" =
    -- "earliest bound", so counts down from the length of the
    -- telescope.
    firstForced :: PatternSubstitution -> Int -> Maybe Int
    firstForced pat level
      | level >= 0 = case lookupS pat level of
        DotP{} -> Just level
        _ -> firstForced pat (level - 1)
      | otherwise = Nothing

-- | Determine which splits should be tried.
splitStrategy :: [ProblemEq] -> [ProblemEq]
splitStrategy = filter shouldSplit
  where
    shouldSplit :: ProblemEq -> Bool
    shouldSplit problem@(ProblemEq p v a) = case p of
      A.LitP{}    -> True
      A.RecP{}    -> True
      A.ConP{}    -> True
      A.EqualP{}  -> True

      A.VarP{}    -> False
      A.WildP{}   -> False
      A.DotP{}    -> False
      A.AbsurdP{} -> False

      A.AsP _ _ p  -> shouldSplit $ problem { problemInPat = p }

      A.ProjP{}       -> __IMPOSSIBLE__
      A.DefP{}        -> __IMPOSSIBLE__
      A.PatternSynP{} -> __IMPOSSIBLE__
      A.WithP{}       -> __IMPOSSIBLE__


-- | The loop (tail-recursive): split at a variable in the problem until problem is solved
checkLHS :: forall tcm a. (MonadTCM tcm, PureTCM tcm, MonadWriter Blocked_ tcm, MonadError TCErr tcm, MonadTrace tcm, MonadReader LHSContext tcm)
  => Maybe QName      -- ^ The name of the definition we are checking.
  -> LHSState a       -- ^ The current state.
  -> tcm a
checkLHS mf = updateModality checkLHS_ where
    -- If the target type is irrelevant or in Prop,
    -- we need to check the lhs in irr. cxt. (see Issue 939).
 updateModality cont st@(LHSState tel ip problem target psplit _) = do
      let m = getModality target
      applyModalityToContext m $ do
        cont $ over (lhsTel . listTel)
                 (map $ inverseApplyModalityButNotQuantity m) st
        -- Andreas, 2018-10-23, issue #3309
        -- the modalities in the clause telescope also need updating.

 checkLHS_ st@(LHSState tel ip problem target psplit ixsplit) = do
  reportSDoc "tc.lhs" 40 $ "tel is" <+> prettyTCM tel
  reportSDoc "tc.lhs" 40 $ "ip is" <+> pretty ip
  reportSDoc "tc.lhs" 40 $ "target is" <+> addContext tel (prettyTCM target)
  if isSolvedProblem problem then
    liftTCM $ (problem ^. problemCont) st
  else do

    reportSDoc "tc.lhs.top" 30 $ vcat
      [ "LHS state: " , nest 2 (prettyTCM st) ]

    unlessM (optPatternMatching <$> getsTC getPragmaOptions) $
      unless (problemAllVariables problem) $
        typeError NeedOptionPatternMatching

    let splitsToTry = splitStrategy $ problem ^. problemEqs

    foldr trySplit trySplitRest splitsToTry >>= \case
      Right st' -> checkLHS mf st'
      -- If no split works, give error from first split.
      -- This is conservative, but might not be the best behavior.
      -- It might be better to print all the errors instead.
      Left (err:_) -> throwError err
      Left []      -> __IMPOSSIBLE__

  where

    trySplit :: ProblemEq
             -> tcm (Either [TCErr] (LHSState a))
             -> tcm (Either [TCErr] (LHSState a))
    trySplit eq tryNextSplit = runExceptT (splitArg eq) >>= \case
      Right st' -> return $ Right st'
      Left err  -> left (err:) <$> tryNextSplit

    -- If there are any remaining user patterns, try to split on them
    trySplitRest :: tcm (Either [TCErr] (LHSState a))
    trySplitRest = case problem ^. problemRestPats of
      []    -> return $ Left []
      (p:_) -> left singleton <$> runExceptT (splitRest p)

    splitArg :: ProblemEq -> ExceptT TCErr tcm (LHSState a)
    -- Split on constructor/literal pattern
    splitArg (ProblemEq p v Dom{unDom = a}) = traceCall (CheckPattern p tel a) $ do

      reportSDoc "tc.lhs.split" 30 $ sep
        [ "split looking at pattern"
        , nest 2 $ "p =" <+> prettyA p
        ]

      -- in order to split, v must be a variable.
      i <- liftTCM $ addContext tel $ ifJustM (isEtaVar v a) return $
             softTypeError $ SplitOnNonVariable v a

      let pos = size tel - (i + 1)
          (delta1, tel'@(ExtendTel dom adelta2)) = splitTelescopeAt pos tel -- TODO:: tel' defined but not used

      p <- expandLitPattern p
      let splitOnPat = \case
            (A.LitP _ l)      -> splitLit delta1 dom adelta2 l
            p@A.RecP{}        -> splitCon delta1 dom adelta2 p Nothing
            p@(A.ConP _ c ps) -> splitCon delta1 dom adelta2 p $ Just c
            p@(A.EqualP _ ts) -> splitPartial delta1 dom adelta2 ts
            A.AsP _ _ p       -> splitOnPat p

            A.VarP{}        -> __IMPOSSIBLE__
            A.WildP{}       -> __IMPOSSIBLE__
            A.DotP{}        -> __IMPOSSIBLE__
            A.AbsurdP{}     -> __IMPOSSIBLE__
            A.ProjP{}       -> __IMPOSSIBLE__
            A.DefP{}        -> __IMPOSSIBLE__
            A.PatternSynP{} -> __IMPOSSIBLE__
            A.WithP{}       -> __IMPOSSIBLE__
      splitOnPat p


    splitRest :: NamedArg A.Pattern -> ExceptT TCErr tcm (LHSState a)
    splitRest p = setCurrentRange p $ do
      reportSDoc "tc.lhs.split" 20 $ sep
        [ "splitting problem rest"
        , nest 2 $ "projection pattern =" <+> prettyA p
        , nest 2 $ "eliminates type    =" <+> prettyTCM target
        ]
      reportSDoc "tc.lhs.split" 80 $ sep
        [ nest 2 $ text $ "projection pattern (raw) = " ++ show p
        ]

      -- @p@ should be a projection pattern projection from @target@
      (orig, ambProjName) <- ifJust (A.isProjP p) return $ addContext tel $ do
        block <- isBlocked target
        softTypeError $ CannotEliminateWithPattern block p (unArg target)

      (projName, comatchingAllowed, recName, projType, ai) <- suspendErrors $ do
        -- Andreas, 2018-10-18, issue #3289: postfix projections do not have hiding
        -- information for their principal argument; we do not parse @{r}.p@ and the like.
        let h = if orig == ProjPostfix then Nothing else Just $ getHiding p
        addContext tel $ disambiguateProjection h ambProjName target

      unless comatchingAllowed $ do
        hardTypeError $ ComatchingDisabledForRecord recName

      -- Compute the new rest type by applying the projection type to 'self'.
      -- Note: we cannot be in a let binding.
      let f = fromMaybe __IMPOSSIBLE__ mf
      let self = Def f $ patternsToElims ip
      target' <- traverse (`piApplyM` self) projType

      -- Compute the new state
      let projP    = applyWhen (orig == ProjPostfix) (setHiding NotHidden) $
                       Arg ai $ Named Nothing (ProjP orig projName)
          ip'      = ip ++ [projP]
          -- drop the projection pattern (already splitted)
          problem' = over problemRestPats (drop 1) problem
      liftTCM $ updateLHSState (LHSState tel ip' problem' target' psplit ixsplit)


    -- Split a Partial.
    --
    -- Example for splitPartial:
    -- @
    --   g : ∀ i j → Partial (i ∨ j) A
    --   g i j (i = 1) = a i j
    --   g i j (j = 1) = b i j
    -- @
    -- leads to, in the first clause:
    -- @
    --   dom   = IsOne (i ∨ j)
    --   ts    = [(i, 1)]
    --   phi   = i
    --   sigma = [1/i]
    -- @
    -- Final clauses:
    -- @
    --   g : ∀ i j → Partial (i ∨ j) A
    --   g 1? j  .itIsOne = a 1 j
    --   g i  1? .itIsOne = b i 1
    -- @
    -- Herein, ? indicates a 'conPFallThrough' pattern.
    --
    -- Example for splitPartial:
    -- @
    --   h : ∀ i j → Partial (i & ¬ j) A
    --   h i j (i = 1) (j = 0)
    --   -- ALT: h i j (i & ¬ j = 1)
    -- @
    -- gives
    -- @
    --   dom = IsOne (i & ¬ j)
    --   ts  = [(i,1), (j,0)]  -- ALT: [(i & ¬ j, 1)]
    --   phi = i & ¬ j
    --   sigma = [1/i,0/j]
    -- @
    --
    -- Example for splitPartial:
    -- @
    --   g : ∀ i j → Partial (i ∨ j) A
    --   g i j (i ∨ j = 1) = a i j
    -- @
    -- leads to, in the first clause:
    -- @
    --   dom   = IsOne (i ∨ j)
    --   ts    = [(i ∨ j, 1)]
    --   phi   = i ∨ j
    --   sigma = fails because several substitutions [[1/i],[1/j]] correspond to phi
    -- @

    splitPartial ::
         Telescope
            -- The types of arguments before the one we split on.
      -> Dom Type
            -- The type of the argument we split on.
      -> Abs Telescope
            -- The types of arguments after the one we split on.
      -> List1 (A.Expr, A.Expr)
            -- [(φ₁ = b1),..,(φn = bn)]
      -> ExceptT TCErr tcm (LHSState a)

    splitPartial delta1 dom adelta2 ts = do

      unless (domIsFinite dom) $ liftTCM $ addContext delta1 $
        softTypeError $ SplitOnPartial dom

      tInterval <- liftTCM $ primIntervalType

      names <- liftTCM $ addContext tel $ do
        LeftoverPatterns{patternVariables = vars} <- getLeftoverPatterns $ problem ^. problemEqs
        return $ take (size delta1) $ fst $ getUserVariableNames tel vars

      -- Problem: The context does not match the checkpoints in checkLHS,
      --          however we still need a proper checkpoint substitution
      --          for checkExpr below.
      --
      -- Solution: partial splits are not allowed when there are
      --           constructor patterns (checked in checkDef), so
      --           newContext is an extension of the definition
      --           context.
      --
      -- i.e.: Given
      --
      --             Γ = context where def is checked, also last checkpoint.
      --
      --       Then
      --
      --             newContext = Γ Ξ
      --             cpSub = raiseS |Ξ|
      --
      lhsCxtSize <- asks lhsContextSize -- size of the context before checkLHS call.
      reportSDoc "tc.lhs.split.partial" 10 $ "lhsCxtSize =" <+> prettyTCM lhsCxtSize

      newContext <- liftTCM $ computeLHSContext names delta1
      reportSDoc "tc.lhs.split.partial" 10 $ "newContext =" <+> prettyTCM newContext

      let cpSub = raiseS $ size newContext - lhsCxtSize

      (gamma,sigma) <- liftTCM $ updateContext cpSub (const newContext) $ do
         ts <- forM ts $ \ (lhs, rhs) -> do
                 reportSDoc "tc.lhs.split.partial" 10 $ "currentCxt =" <+> (prettyTCM =<< getContext)
                 reportSDoc "tc.lhs.split.partial" 10 $ text "t, u (Expr) =" <+> prettyTCM (lhs, rhs)
                 t <- checkExpr lhs tInterval
                 u <- checkExpr rhs tInterval
                 reportSDoc "tc.lhs.split.partial" 10 $ text "t, u        =" <+> pretty (t, u)
                 reduce u >>= intervalView >>= \case
                   IZero -> primINeg <@> pure t
                   IOne  -> return t
                   _     -> typeError $ ExpectedIntervalLiteral rhs
         -- Example: ts = (i=0) (j=1) will result in phi = ¬ i & j
         phi <- foldl (\ x y -> primIMin <@> x <@> y) primIOne (fmap pure ts)
         reportSDoc "tc.lhs.split.partial" 10 $ text "phi           =" <+> prettyTCM phi
         reportSDoc "tc.lhs.split.partial" 30 $ text "phi           =" <+> pretty phi
         phi <- reduce phi
         reportSDoc "tc.lhs.split.partial" 10 $ text "phi (reduced) =" <+> prettyTCM phi
         refined <- forallFaceMaps phi (\ bs m t -> typeError $ GenericError $ "face blocked on meta")
                            (\_ sigma -> (,sigma) <$> getContextTelescope)
         case refined of
           [(gamma,sigma)] -> return (gamma,sigma)
           []              -> typeError $ GenericError $ "The face constraint is unsatisfiable."
           _               -> typeError $ GenericError $ "Cannot have disjunctions in a face constraint."
      itisone <- liftTCM primItIsOne
      -- substitute the literal in p1 and dpi
      reportSDoc "tc.lhs.faces" 60 $ text $ show sigma

      let oix = size adelta2 -- de brujin index of IsOne
          o_n = fromMaybe __IMPOSSIBLE__ $
            findIndex (\ x -> case namedThing (unArg x) of
                                   VarP _ x -> dbPatVarIndex x == oix
                                   _        -> False) ip
          delta2' = absApp adelta2 itisone
          delta2 = applySubst sigma delta2'
          mkConP (Con c _ [])
             = ConP c (noConPatternInfo { conPType = Just (Arg defaultArgInfo tInterval)
                                              , conPFallThrough = True })
                          []
          mkConP (Var i []) = VarP defaultPatternInfo (DBPatVar "x" i)
          mkConP _          = __IMPOSSIBLE__
          rho0 = fmap mkConP sigma

          rho    = liftS (size delta2) $ consS (DotP defaultPatternInfo itisone) rho0

          delta'   = abstract gamma delta2
          eqs'     = applyPatSubst rho $ problem ^. problemEqs
          ip'      = applySubst rho ip
          target'  = applyPatSubst rho target

      -- Compute the new state
      let problem' = set problemEqs eqs' problem
      reportSDoc "tc.lhs.split.partial" 60 $ text (show problem')
      liftTCM $ updateLHSState (LHSState delta' ip' problem' target' (psplit ++ [Just o_n]) ixsplit)


    splitLit :: Telescope      -- The types of arguments before the one we split on
             -> Dom Type       -- The type of the literal we split on
             -> Abs Telescope  -- The types of arguments after the one we split on
             -> Literal        -- The literal written by the user
             -> ExceptT TCErr tcm (LHSState a)
    splitLit delta1 dom@Dom{domInfo = info, unDom = a} adelta2 lit = do
      let delta2 = absApp adelta2 (Lit lit)
          delta' = abstract delta1 delta2
          rho    = singletonS (size delta2) (litP lit)
          -- Andreas, 2015-06-13 Literals are closed, so no need to raise them!
          -- rho    = liftS (size delta2) $ singletonS 0 (Lit lit)
          -- rho    = [ var i | i <- [0..size delta2 - 1] ]
          --       ++ [ raise (size delta2) $ Lit lit ]
          --       ++ [ var i | i <- [size delta2 ..] ]
          eqs'     = applyPatSubst rho $ problem ^. problemEqs
          ip'      = applySubst rho ip
          target'  = applyPatSubst rho target

      -- Andreas, 2010-09-07 cannot split on irrelevant args
      unless (usableRelevance info) $
        addContext delta1 $ softTypeError $ SplitOnIrrelevant dom

      -- Andreas, 2018-10-17, we can however split on erased things
      -- if there is a single constructor (checked in Coverage).
      --
      -- Thus, no checking of (usableQuantity info) here.

      unlessM (splittableCohesion info) $
        addContext delta1 $ softTypeError $ SplitOnUnusableCohesion dom

      unless (splittablePolarity (getModalPolarity info)) $
        addContext delta1 $ softTypeError $ SplitOnUnusablePolarity dom

      -- check that a is indeed the type of lit (otherwise fail softly)
      -- if not, fail softly since it could be instantiated by a later split.
      suspendErrors $ equalType a =<< litType lit

      -- Compute the new state
      let problem' = set problemEqs eqs' problem
      liftTCM $ updateLHSState (LHSState delta' ip' problem' target' psplit ixsplit)


    splitCon :: Telescope      -- The types of arguments before the one we split on
             -> Dom Type       -- The type of the constructor we split on
             -> Abs Telescope  -- The types of arguments after the one we split on
             -> A.Pattern      -- The pattern written by the user
             -> Maybe AmbiguousQName  -- @Just c@ for a (possibly ambiguous) constructor @c@, or
                                      -- @Nothing@ for a record pattern
             -> ExceptT TCErr tcm (LHSState a)
    splitCon delta1 dom@Dom{domInfo = info, unDom = a} adelta2 focusPat ambC = do
      let delta2 = absBody adelta2

      reportSDoc "tc.lhs.split" 10 $ vcat
        [ "checking lhs"
        , nest 2 $ "tel =" <+> prettyTCM tel
        , nest 2 $ "rel =" <+> text (show $ getRelevance info)
        , nest 2 $ "mod =" <+> text (show $ getModality  info)
        ]

      reportSDoc "tc.lhs.split" 15 $ vcat
        [ "split problem"
        , nest 2 $ vcat
          [ "delta1 = " <+> prettyTCM delta1
          , "a      = " <+> addContext delta1 (prettyTCM a)
          , "delta2 = " <+> addContext delta1
                              (addContext ("x" :: String, dom) (prettyTCM delta2))
          ]
        ]

      -- We cannot split on (shape-)irrelevant arguments.
      reportSLn "tc.lhs.split" 30 $ "split ConP: relevance is " ++ show (getRelevance info)
      unless (usableRelevance info) $ addContext delta1 $
        softTypeError $ SplitOnIrrelevant dom

      -- Andreas, 2018-10-17, we can however split on erased things
      -- if there is a single constructor (checked in Coverage).
      --
      -- Thus, no checking of (usableQuantity info) here.

      unlessM (splittableCohesion info) $
        addContext delta1 $ softTypeError $ SplitOnUnusableCohesion dom

      unless (splittablePolarity (getModalPolarity info)) $
        addContext delta1 $ softTypeError $ SplitOnUnusablePolarity dom

      -- Should we attempt to compute a left inverse for this clause? When
      -- --cubical-compatible --flat-split is given, we don't generate a
      -- left inverse (at all). This means that, when the coverage checker
      -- gets to the clause this was in, it won't generate a (malformed!)
      -- transpX clause for @♭ matching.
      -- TODO(Amy): properly support transpX when @♭ stuff is in the
      -- context.
      let genTrx = boolToMaybe ((getCohesion info == Flat)) SplitOnFlat

      -- We should be at a data/record type
      (dr, d, s, pars, ixs) <- addContext delta1 $ isDataOrRecordType a
      let isRec = case dr of
            IsData{}   -> False
            IsRecord{} -> True

      checkMatchingAllowed d dr  -- No splitting on coinductive constructors.

      -- Issue #7503: use principal sort for checking if split is ok
      let a' = set lensSort s a
      addContext delta1 $ checkSortOfSplitVar dr a' delta2 (Just target)

      -- Jesper, 2019-09-13: if the data type we split on is a strict
      -- set, we locally enable --with-K during unification.
      withKIfStrict <- reduce (getSort a) <&> \ dsort ->
        applyWhen (isStrictDataSort dsort) $ locallyTC eSplitOnStrict $ const True

      -- The constructor should construct an element of this datatype
      (c :: ConHead, b :: Type) <- liftTCM $ addContext delta1 $ case ambC of
        Just ambC -> disambiguateConstructor ambC d pars
        Nothing   -> getRecordConstructor d pars a

      -- Don't split on lazy (non-eta) constructor
      case focusPat of
        A.ConP cpi _ _ | A.conPatLazy cpi == A.ConPatLazy ->
          unlessM (isEtaRecord d) $ softTypeError $ ForcedConstructorNotInstantiated focusPat
        _ -> return ()

      -- The type of the constructor will end in an application of the datatype
      (TelV gamma (El _ ctarget), boundary) <- liftTCM $ telViewPathBoundaryP b
      let Def d' es' = ctarget
          cixs = drop (size pars) $ fromMaybe __IMPOSSIBLE__ $ allApplyElims es'

      -- Δ₁Γ ⊢ boundary
      reportSDoc "tc.lhs.split.con" 50 $ text "  boundary = " <+> prettyTCM boundary

      unless (d == d') {-'-} __IMPOSSIBLE__

      -- Get names for the constructor arguments from the user patterns
      gamma <- liftTCM $ case focusPat of
        A.ConP _ _ ps -> do
          ps <- insertImplicitPatterns ExpandLast ps gamma
          return $ useNamesFromPattern ps gamma
        A.RecP _ fs -> do
          RecordDefn def <- theDef <$> getConstInfo d
          let axs = map argFromDom $ recordFieldNames def
          ps <- insertMissingFieldsFail A.RecStyleBrace d (const $ A.WildP empty) fs axs
          ps <- insertImplicitPatterns ExpandLast ps gamma
          return $ useNamesFromPattern ps gamma
        _ -> __IMPOSSIBLE__

      -- Andreas 2010-09-07  propagate relevance info to new vars
      -- Andreas 2018-10-17  propagate modality
      let updMod = composeModality (getModality info)
      gamma <- return $ mapModality updMod <$> gamma

      -- Get the type of the datatype.
      da <- (`piApply` pars) . defType <$> getConstInfo d
      reportSDoc "tc.lhs.split" 30 $ "  da = " <+> prettyTCM da

      reportSDoc "tc.lhs.top" 15 $ addContext delta1 $
        sep [ "preparing to unify"
            , nest 2 $ vcat
              [ "c      =" <+> prettyTCM c <+> ":" <+> prettyTCM b
              , "d      =" <+> prettyTCM (Def d (map Apply pars)) <+> ":" <+> prettyTCM da
              , "isRec  =" <+> (text . show) isRec
              , "gamma  =" <+> prettyTCM gamma
              , "pars   =" <+> brackets (fsep $ punctuate comma $ map prettyTCM pars)
              , "ixs    =" <+> brackets (fsep $ punctuate comma $ map prettyTCM ixs)
              , "cixs   =" <+> addContext gamma (brackets (fsep $ punctuate comma $ map prettyTCM cixs))
              ]
            ]
                 -- We ignore forcing for make-case
      cforced <- ifM (viewTC eMakeCase) (return []) $
                 {-else-} defForced <$> getConstInfo (conName c)

      let delta1Gamma = delta1 `abstract` gamma
          da'  = raise (size gamma) da
          ixs' = raise (size gamma) ixs
          -- Variables in Δ₁ are not forced, since the unifier takes care to not introduce forced
          -- variables.
          forced = replicate (size delta1) NotForced ++ cforced

      -- All variables are flexible.
      let flex = allFlexVars forced $ delta1Gamma

      -- Unify constructor target and given type (in Δ₁Γ)
      -- Given: Δ₁  ⊢ D pars : Φ → Setᵢ
      --        Δ₁  ⊢ c      : Γ → D pars cixs
      --        Δ₁  ⊢ ixs    : Φ
      --        Δ₁Γ ⊢ cixs   : Φ
      -- unification of ixs and cixs in context Δ₁Γ gives us a telescope Δ₁'
      -- and a substitution ρ₀ such that
      --        Δ₁' ⊢ ρ₀ : Δ₁Γ
      --        Δ₁' ⊢ (ixs)ρ₀ ≡ (cixs)ρ₀ : Φρ₀
      -- We can split ρ₀ into two parts ρ₁ and ρ₂, giving
      --        Δ₁' ⊢ ρ₁ : Δ₁
      --        Δ₁' ⊢ ρ₂ : Γρ₁
      -- Application of the constructor c gives
      --        Δ₁' ⊢ (c Γ)(ρ₀) : (D pars cixs)(ρ₁;ρ₂)
      -- We have
      --        cixs(ρ₁;ρ₂)
      --         ≡ cixs(ρ₀)   (since ρ₀=ρ₁;ρ₂)
      --         ≡ ixs(ρ₀)    (by unification)
      --         ≡ ixs(ρ₁)    (since ixs doesn't actually depend on Γ)
      -- so     Δ₁' ⊢ (c Γ)(ρ₀) : (D pars ixs)ρ₁
      -- Putting this together with ρ₁ gives ρ₃ = ρ₁;c ρ₂
      --        Δ₁' ⊢ ρ₁;(c Γ)(ρ₀) : Δ₁(x : D vs ws)
      -- and lifting over Δ₂ gives the final substitution ρ = ρ₃;Δ₂
      -- from Δ' = Δ₁';Δ₂ρ₃
      --        Δ' ⊢ ρ : Δ₁(x : D vs ws)Δ₂

      -- Andrea 2019-07-17 propagate the Cohesion to the equation telescope
      -- TODO: should we propagate the modality in general?
      -- See also Coverage checking.
      da' <- addContext delta1Gamma $ do
             let updCoh = composeCohesion (getCohesion info)
             TelV tel dt <- telView da'
             return $ abstract (mapCohesion updCoh <$> tel) a

      let stuck b errs = softTypeError $ SplitError $
            UnificationStuck b (conName c) (delta1 `abstract` gamma) cixs ixs' errs

      liftTCM (withKIfStrict $ unifyIndices genTrx delta1Gamma flex da' cixs ixs') >>= \case

        -- Mismatch.  Report and abort.
        NoUnify neg -> hardTypeError $ ImpossibleConstructor (conName c) neg

        UnifyBlocked block -> stuck (Just block) []

        -- Unclear situation.  Try next split.
        UnifyStuck errs -> stuck Nothing errs

        -- Success.
        Unifies (delta1',rho0,es) -> do

          reportSDoc "tc.lhs.top" 15 $ "unification successful"
          reportSDoc "tc.lhs.top" 20 $ nest 2 $ vcat
            [ "delta1' =" <+> prettyTCM delta1'
            , "rho0    =" <+> addContext delta1' (prettyTCM rho0)
            , "es      =" <+> addContext delta1' (prettyTCM $ (fmap . fmap . fmap) patternToTerm es)
            ]

          -- split substitution into part for Δ₁ and part for Γ
          let (rho1,rho2) = splitS (size gamma) rho0

          reportSDoc "tc.lhs.top" 20 $ addContext delta1' $ nest 2 $ vcat
            [ "rho1    =" <+> prettyTCM rho1
            , "rho2    =" <+> prettyTCM rho2
            ]

          -- Andreas, 2010-09-09, save the type.
          -- It is relative to Δ₁, but it should be relative to Δ₁'
          let a' = applyPatSubst rho1 a

          -- Also remember if we are a record pattern.
          let cpi = ConPatternInfo { conPInfo   = PatternInfo PatOCon []
                                   , conPRecord = isRec
                                   , conPFallThrough = False
                                   , conPType   = Just $ Arg info a'
                                   , conPLazy   = False } -- Don't mark eta-record matches as lazy (#4254)

          -- compute final context and substitution
          let crho    = ConP c cpi $ applySubst rho0 $ (telePatterns gamma boundary)
              rho3    = consS crho rho1
              delta2' = applyPatSubst rho3 delta2
              delta'  = delta1' `abstract` delta2'
              rho     = liftS (size delta2) rho3

          reportSDoc "tc.lhs.top" 20 $ addContext delta1' $ nest 2 $ vcat
            [ "crho    =" <+> prettyTCM crho
            , "rho3    =" <+> prettyTCM rho3
            , "delta2' =" <+> prettyTCM delta2'
            ]
          reportSDoc "tc.lhs.top" 70 $ addContext delta1' $ nest 2 $ vcat
            [ "crho    =" <+> pretty crho
            , "rho3    =" <+> pretty rho3
            , "delta2' =" <+> pretty delta2'
            ]

          reportSDoc "tc.lhs.top" 15 $ nest 2 $ vcat
            [ "delta'  =" <+> prettyTCM delta'
            , "rho     =" <+> addContext delta' (prettyTCM rho)
            ]

          -- Compute the new out patterns and target type.
          let ip'      = applySubst rho ip
              target'  = applyPatSubst rho target

          -- Update the problem equations
          let eqs' = applyPatSubst rho $ problem ^. problemEqs
              problem' = set problemEqs eqs' problem

          -- The result type's quantity is set to 0 for erased
          -- constructors, but not if the match is made in an erased
          -- position, or if the original constructor definition is
          -- not erased.
          cq <- getQuantity <$> getOriginalConstInfo (conName c)
          let target'' = mapQuantity updResMod target'
                where
                  erased = case getQuantity info of
                    Quantity0{} -> True
                    Quantity1{} -> __IMPOSSIBLE__
                    Quantityω{} -> False
                  -- either sets to Quantity0 or is the identity.
                  updResMod q =
                    case cq of
                     _ | erased  -> q
                     Quantity0{} -> composeQuantity cq q
                                 -- zero-out, preserves origin
                     Quantity1{} -> __IMPOSSIBLE__
                     Quantityω{} -> q

          unless (null ixs) $
            whenM (withoutKOption `or2M` cubicalCompatibleOption) $ do
              mod <- currentModality
              lhsRng <- asks lhsRange
              liftTCM $ addContext delta' $
                conSplitModalityCheck lhsRng mod rho (length delta2) tel (unArg target)

          -- if rest type reduces,
          -- extend the split problem by previously not considered patterns
          st' <- liftTCM $ updateLHSState $ LHSState delta' ip' problem' target'' psplit (ixsplit || not (null ixs))

          reportSDoc "tc.lhs.top" 12 $ sep
            [ "new problem from rest"
            , nest 2 $ vcat
              [ "delta'  =" <+> prettyTCM (st' ^. lhsTel)
              , "eqs'    =" <+> addContext (st' ^. lhsTel) (prettyTCM $ st' ^. (lhsProblem . problemEqs))
              , "ip'     =" <+> addContext (st' ^. lhsTel) (pretty $ st' ^. lhsOutPat)
              ]
            ]
          return st'


-- | Ensures that we are not performing pattern matching on coinductive constructors.

checkMatchingAllowed :: (MonadTCError m)
  => QName         -- ^ The name of the data or record type the constructor belongs to.
  -> DataOrRecord  -- ^ Information about data or (co)inductive (no-)eta-equality record.
  -> m ()
checkMatchingAllowed d = \case
  IsRecord InductionAndEta { recordInduction=ind, recordEtaEquality=eta }
    | Just CoInductive <- ind -> typeError SplitOnCoinductive
    | not $ patternMatchingAllowed eta -> typeError $ SplitOnNonEtaRecord d
    | otherwise -> return ()
  IsData -> return ()

-- | When working with a monad @m@ implementing @MonadTCM@ and @MonadError TCErr@,
--   @suspendErrors f@ performs the TCM action @f@ but catches any errors and throws
--   them in the monad @m@ instead.
suspendErrors :: (MonadTCM m, MonadError TCErr m) => TCM a -> m a
suspendErrors f = do
  ok <- liftTCM $ (Right <$> f) `catchError` (return . Left)
  either throwError return ok

-- | A more direct implementation of the specification
--   @softTypeError err == suspendErrors (typeError err)@
softTypeError :: (HasCallStack, ReadTCState m, MonadError TCErr m, MonadTCEnv m) => TypeError -> m a
softTypeError err = withCallerCallStack $ \loc ->
  throwError =<< typeError' loc err

-- | A convenient alias for @liftTCM . typeError@. Throws the error directly
--   in the TCM even if there is a surrounding monad also implementing
--   @MonadError TCErr@.
hardTypeError :: (HasCallStack, MonadTCM m) => TypeError -> m a
hardTypeError = withCallerCallStack $ \loc -> liftTCM . typeError' loc

type DataOrRecord = DataOrRecord' InductionAndEta

-- | Check if the type is a data or record type and return its name,
--   definition, sort, parameters, and indices. Fails softly if the type could become
--   a data/record type by instantiating a variable/metavariable, or fail hard
--   otherwise.
isDataOrRecordType
  :: (MonadTCM m, PureTCM m)
  => Type
  -> ExceptT TCErr m (DataOrRecord, QName, Sort, Args, Args)
       -- ^ The 'Args' are parameters and indices.

isDataOrRecordType a0 = ifBlocked a0 blocked $ \case
  ReallyNotBlocked -> \ a -> case unEl a of

    -- Subcase: split type is a Def.
    Def d es -> liftTCM (getConstInfo d) >>= \def -> case theDef def of

      Datatype{dataPars = np, dataSort = s} -> do

        whenM (isInterval a) $ hardTypeError =<< notData

        let (pars, ixs) = splitAt np $ fromMaybe __IMPOSSIBLE__ $ allApplyElims es
        return (IsData, d, s, pars, ixs)

      Record{ recInduction, recEtaEquality' } -> do
        let pars = fromMaybe __IMPOSSIBLE__ $ allApplyElims es
        s <- shouldBeSort =<< defType def `piApplyM` pars
        return (IsRecord InductionAndEta {recordInduction=recInduction, recordEtaEquality=recEtaEquality' }, d, s, pars, [])

      -- Issue #2253: the data type could be abstract.
      AbstractDefn{} -> hardTypeError $ SplitOnAbstract d

      -- the type could be an axiom
      Axiom{} -> hardTypeError =<< notData

      -- Can't match before we have the definition
      DataOrRecSig{} -> hardTypeError $ SplitOnUnchecked d

      -- Issue #2997: the type could be a Def that does not reduce for some reason
      -- (abstract, failed termination checking, NON_TERMINATING, ...)
      Function{}    -> hardTypeError =<< notData

      Constructor{} -> __IMPOSSIBLE__

      -- Issue #3620: Some primitives are types too.
      -- Not data though, at least currently 11/03/2018.
      Primitive{}   -> hardTypeError =<< notData

      PrimitiveSort{} -> hardTypeError =<< notData

      GeneralizableVar{} -> __IMPOSSIBLE__

    -- variable: fail softly
    Var{}      -> softTypeError =<< notData
    MetaV{}    -> __IMPOSSIBLE__  -- That is handled in @blocked@.

    -- pi or sort: fail hard
    Pi{}       -> hardTypeError =<< notData
    Sort{}     -> hardTypeError =<< notData

    Lam{}      -> __IMPOSSIBLE__
    Lit{}      -> __IMPOSSIBLE__
    Con{}      -> __IMPOSSIBLE__
    Level{}    -> __IMPOSSIBLE__
    DontCare{} -> __IMPOSSIBLE__
    Dummy s _  -> __IMPOSSIBLE_VERBOSE__ s

  -- neutral type: fail softly
  StuckOn{}     -> \ _a -> softTypeError =<< notData
  AbsurdMatch{} -> \ _a -> softTypeError =<< notData

  -- missing clauses: fail hard
  -- TODO: postpone checking of the whole clause until later?
  MissingClauses{} -> \ _a -> hardTypeError =<< notData

  -- underapplied type: should not happen
  Underapplied{} -> __IMPOSSIBLE__

  where
  notData      = liftTCM $ SplitError . NotADatatype <$> buildClosure a0
  blocked b _a = softTypeError =<< do liftTCM $ SplitError . BlockedType b <$> buildClosure a0

-- | Get the constructor of the given record type together with its type.
--   Throws an error if the type is not a record type.
getRecordConstructor
  :: QName  -- ^ Name @d@ of the record type
  -> Args   -- ^ Parameters @pars@ of the record type
  -> Type   -- ^ The record type @Def d pars@ (for error reporting)
  -> TCM (ConHead, Type)
getRecordConstructor d pars a = do
  con <- (theDef <$> getConstInfo d) >>= \case
    Record{recConHead = con} -> return $ killRange con
    _ -> typeError $ ShouldBeRecordType a
  b <- (`piApply` pars) . defType <$> getConstInfo (conName con)
  return (con, b)


-- | Disambiguate a projection based on the record type it is supposed to be
--   projecting from. Returns the unambiguous projection name and its type.
--   Throws an error if the type is not a record type.
disambiguateProjection
  :: Maybe Hiding   -- ^ Hiding info of the projection's principal argument.
                    --   @Nothing@ if 'Postfix' projection.
  -> AmbiguousQName -- ^ Name of the projection to be disambiguated.
  -> Arg Type       -- ^ Record type we are projecting from.
  -> TCM (QName, Bool, QName, Arg Type, ArgInfo)
       -- ^ @Bool@ signifies whether copattern matching is allowed at
       --   the inferred record type.
disambiguateProjection h ambD@(AmbQ ds) b = do
  -- If the target is not a record type, that's an error.
  -- It could be a meta, but since we cannot postpone lhs checking, we crash here.
  caseMaybeM (liftTCM $ isRecordType $ unArg b) notRecord
    \ (r, vs, RecordData{ _recFields = fs, _recInduction = ind, _recEtaEquality' = eta }) -> do
      reportSDoc "tc.lhs.split" 20 $ sep
        [ "we are of record type r  = " <> pure (P.pretty r)
        , "applied to parameters vs = " <> prettyTCM vs
        , "and have fields       fs = " <> pure (P.pretty $ map argFromDom fs)
        ]
      let comatching = ind == Just CoInductive
                    || copatternMatchingAllowed eta
      -- Try the projection candidates.
      -- First, we try to find a disambiguation that doesn't produce
      -- any new constraints.
      tryDisambiguate False fs r vs comatching $ \ _ ->
          -- If this fails, we try again with constraints, but we require
          -- the solution to be unique.
          tryDisambiguate True fs r vs comatching $ \case
            (err:_, [] ) -> throwError err
            ([]   , [] ) -> __IMPOSSIBLE__
            (_    , [_]) -> __IMPOSSIBLE__
            (_    , (d,_) : (d1,_) : disambs) ->
              typeError $ AmbiguousProjection d $ d1 :| map fst disambs
  where
    tryDisambiguate constraintsOk fs r vs comatching failure = do
      -- Note that tryProj wraps TCM in an ExceptT, collecting errors
      -- instead of throwing them to the user immediately.
      disambiguations :: List1 (Either TCErr (QName, (Arg Type, ArgInfo, Maybe TCState)))
        <- mapM (runExceptT . tryProj constraintsOk fs r vs) ds
      case List1.partitionEithers disambiguations of
        (_ , (d, (a, ai, mst)) : disambs) | constraintsOk <= null disambs -> do
          mapM_ putTC mst -- Activate state changes
          -- From here, we have the correctly disambiguated projection.
          -- For highlighting, we remember which name we disambiguated to.
          -- This is safe here (fingers crossed) as we won't decide on a
          -- different projection even if we backtrack and come here again.
          liftTCM $ storeDisambiguatedProjection d
          return (d, comatching, r, a, ai)
        other -> failure other

    notRecord = wrongProj $ List1.head ds

    wrongProj :: (MonadTCM m, MonadError TCErr m, ReadTCState m) => QName -> m a
    wrongProj d = softTypeError =<< do
      liftTCM $ if isAmbiguous ambD then CannotEliminateWithProjection b True <$> dropTopLevelModule d
                else pure $ CannotEliminateWithProjection b False d

    tryProj
      :: Bool                 -- Are we allowed to create new constraints?
      -> [Dom QName]          -- Fields of record type under consideration.
      -> QName                -- Name of record type we are eliminating.
      -> Args                 -- Parameters of record type we are eliminating.
      -> QName                -- Candidate projection.
      -> ExceptT TCErr TCM (QName, (Arg Type, ArgInfo, Maybe TCState))
           -- TCState contains possibly new constraints/meta solutions.
    tryProj constraintsOk fs r vs d0 = isProjection d0 >>= \case
      -- Not a projection
      Nothing -> wrongProj d0
      Just proj -> do
        let d = projOrig proj

        -- Andreas, 2015-05-06 issue 1413 projProper=Nothing is not impossible
        qr <- maybe (wrongProj d) return $ projProper proj

        -- If projIndex==0, then the projection is already applied
        -- to the record value (like in @open R r@), and then it
        -- is no longer a projection but a record field.
        when (null $ projLams proj) $ wrongProj d
        reportSLn "tc.lhs.split" 90 "we are a projection pattern"
        -- If the target is not a record type, that's an error.
        -- It could be a meta, but since we cannot postpone lhs checking, we crash here.
        reportSDoc "tc.lhs.split" 20 $ sep
          [ text $ "proj                  d0 = " ++ prettyShow d0
          , text $ "original proj         d  = " ++ prettyShow d
          ]
        -- Get the field decoration.
        -- If the projection pattern name @d@ is not a field name,
        -- we have to try the next projection name.
        -- If this was not an ambiguous projection, that's an error.
        argd <- maybe (wrongProj d) return $ List.find ((d ==) . unDom) fs

        -- Issue4998: This used to use the hiding from the principal argument, but this is not
        -- relevant for the ArgInfo of the clause rhs. We return that separately so we can set the
        -- correct hiding for the projection pattern in splitRest above.
        let ai = getArgInfo argd

        reportSDoc "tc.lhs.split" 20 $ vcat
          [ text $ "original proj relevance  = " ++ show (getRelevance argd)
          , text $ "original proj quantity   = " ++ show (getQuantity  argd)
          ]
        -- Andreas, 2016-12-31, issue #2374:
        -- We can also disambiguate by hiding info.
        -- Andreas, 2018-10-18, issue #3289: postfix projections have no hiding info.
        unless (caseMaybe h True $ sameHiding $ projArgInfo proj) $
          softTypeError $ WrongHidingInProjection d

        -- Andreas, 2016-12-31, issue #1976: Check parameters.
        let chk = checkParameters qr r vs
        mst <- suspendErrors $
          if constraintsOk then Just . snd <$> localTCStateSaving chk
          else Nothing <$ nonConstraining chk

        -- Get the type of projection d applied to "self"
        dType <- liftTCM $ defType <$> getConstInfo d  -- full type!
        reportSDoc "tc.lhs.split" 20 $ sep
          [ "we are being projected by dType = " <+> prettyTCM dType
          ]
        projType <- liftTCM $ dType `piApplyM` vs
        return (d0, (Arg ai projType, projArgInfo proj, mst))

-- | Disambiguate a constructor based on the data type it is supposed to be
--   constructing. Returns the unambiguous constructor name and its type.
--   Precondition: type should be a data/record type.
disambiguateConstructor
  :: AmbiguousQName    -- ^ The name of the constructor to be disambiguated.
  -> QName             -- ^ Name of the datatype.
  -> Args              -- ^ Parameters of the datatype
  -> TCM (ConHead, Type)
disambiguateConstructor ambC@(AmbQ cs) d pars = do
  d <- canonicalName d
  cons <- theDef <$> getConstInfo d >>= \case
    def@Datatype{} -> return $ dataCons def
    def@Record{}   -> return $ [conName $ recConHead def]
    _              -> __IMPOSSIBLE__

  -- First, try do disambiguate with nonConstraining,
  -- if that fails, try again allowing constraint/solution generation.
  tryDisambiguate False d cons $ \ _ ->
    tryDisambiguate True d cons $ \case
        ([]   , [] ) -> __IMPOSSIBLE__
        (err:_, [] ) -> throwError err
        -- If all disambiguations point to the same original constructor
        -- meaning that only the parameters may differ,
        -- then throw more specific error.
        (_    , [_]) -> typeError $ CantResolveOverloadedConstructorsTargetingSameDatatype d cs
        (_    , (d0@((c,_,_) :| _) : d1 : ds)) -> typeError $
          AmbiguousConstructor c $ fmap (conName . snd3) $ List2.concat21 $ List2 d0 d1 ds

  where
    tryDisambiguate
      :: Bool     -- May we constrain/solve metas to arrive at unique disambiguation?
      -> QName    -- Data/record type.
      -> [QName]  -- Its constructor(s).
      -> ( ( [TCErr]
           , [List1 (QName, ConHead, (Type, Maybe TCState))]
           )
           -> TCM (ConHead, Type) )  -- Failure continuation, taking
                                     -- possible disambiguations
                                     -- grouped by the original
                                     -- constructor name in 'ConHead'.
      -> TCM (ConHead, Type)  -- Unique disambiguation and its type.
    tryDisambiguate constraintsOk d cons failure = do
      reportSDoc "tc.lhs.disamb" 30 $ sep $ List.concat $
        [ [ "tryDisambiguate" ]
        , if constraintsOk then [ "(allowing new constraints)" ] else empty
        , map (nest 2 . pretty) $ List1.toList cs
        , [ "against" ]
        , map (nest 2 . pretty) cons
        ]
      disambiguations <- mapM (runExceptT . tryCon constraintsOk cons d pars) cs
      -- Q: can we be more lazy, like using the ListT monad?
      -- Andreas, 2020-06-17: Not really, since we need to make sure
      -- that only a single candidate remains, and if not,
      -- report all alternatives in the error message.
      let (errs, fits0) = List1.partitionEithers disambiguations
      reportSDoc "tc.lhs.disamb" 40 $ vcat $ do
        let hideSt (c0,c,(a,mst)) = (c0, c, (a, ("(state change)" :: String) <$ mst))
        "remaining candidates: " : map (nest 2 . prettyTCM . hideSt) fits0
      dedupCons fits0 >>= \case

        -- Single candidate remains.
        [ (c0,c,(a,mst)) :| [] ] -> do
          reportSDoc "tc.lhs.disamb" 30 $ sep $
            [ "tryDisambiguate suceeds with"
            , pretty c0
            , ":"
            , prettyTCM a
            ]
          -- Andreas, 2020-06-16, issue #4135
          -- If disambiguation succeeded with new constraints/solutions,
          -- put them into action.
          whenJust mst putTC
          -- If there are multiple candidates for the constructor pattern, exactly one of
          -- which type checks, remember our choice for highlighting info.
          when (isAmbiguous ambC) $ liftTCM $
            storeDisambiguatedConstructor (conInductive c) c0
          return (c,a)

        -- Either no candidate constructor in 'cs' type checks, or multiple candidates
        -- type check.
        groups -> failure (errs, groups)

    abstractConstructor c = softTypeError $
      AbstractConstructorNotInScope c

    wrongDatatype c d = softTypeError $
      ConstructorPatternInWrongDatatype c d

    tryCon
      :: Bool        -- Are we allowed to constrain metas?
      -> [QName]     -- Constructors of data type under consideration.
      -> QName       -- Name of data/record type we are eliminating.
      -> Args        -- Parameters of data/record type we are eliminating.
      -> QName       -- Candidate constructor.
      -> ExceptT TCErr TCM (QName, ConHead, (Type, Maybe TCState))
           -- If this candidate succeeds, return its disambiguation
           -- its type, and maybe the state obtained after checking it
           -- (which may contain new constraints/solutions).
    tryCon constraintsOk cons d pars c = getConstInfo' c >>= \case
      Left (SigUnknown err)     -> __IMPOSSIBLE__
      Left SigCubicalNotErasure -> __IMPOSSIBLE__
      Left SigAbstract          -> abstractConstructor c
      Right def                 -> do
        let con = conSrcCon (theDef def) `withRangeOf` c
        unless (conName con `elem` cons) $ wrongDatatype c d

        -- Andreas, 2013-03-22 fixing issue 279
        -- To resolve ambiguous constructors, Agda always looks up
        -- their original definition and reconstructs the parameters
        -- from the type @Def d vs@ we check against.
        -- However, the constructor could come from a module instantiation
        -- with some of the parameters already fixed.
        -- Agda did not make sure the two parameter lists coincide,
        -- so we add a check here.
        -- I guess this issue could be solved more systematically,
        -- but the extra check here is non-invasive to the existing code.
        -- Andreas, 2016-12-31 fixing issue #1975
        -- Do this also for constructors which were originally ambiguous.
        let chk = checkConstructorParameters c d pars
        mst <- suspendErrors $
          if constraintsOk then Just . snd <$> localTCStateSaving chk
          else Nothing <$ nonConstraining chk

        -- Get the type from the original constructor.
        -- Andreas, 2020-06-17 TODO:
        -- Couldn't we return this type from checkConstructorParameters?
        cType <- (`piApply` pars) . defType <$> getConInfo con

        return (c, con, (cType, mst))

    -- This deduplication identifies different names of the same
    -- constructor, ensuring that the "ambiguous constructor" error
    -- does not fire for the case described in #4130.
    --
    -- Andreas, 2020-06-17, issue #4135:
    -- However, we need to distinguish different occurrences
    -- of the same original constructor if it is used
    -- with different data parameters, as recorded in the @Type@.
    dedupCons ::
      forall a.       [ (a, ConHead, (Type, Maybe TCState)) ]
         -> TCM [ List1 (a, ConHead, (Type, Maybe TCState)) ]
    dedupCons cands = do
      -- Group candidates by original constructor name.
      let groups = List1.groupWith (conName . snd3) cands
      -- Eliminate duplicates (same type) from groups.
      mapM (List1.nubM (cmpM `on` thd3)) groups
      where
      -- The types come possibly with their own state.
      cmpM (a1, mst1) (a2, mst2) = do
        let cmpTypes = tryConversion $ equalType a1 a2
        case (mst1, mst2) of
          (Nothing, Nothing) -> cmpTypes
          (Just st, Nothing) -> inState st cmpTypes
          (Nothing, Just st) -> inState st cmpTypes
          -- Andreas, 2020-06-17, issue #4135.
          -- If the state has diverged into two states we give up.
          -- For instance, one state may say `?0 := true`
          -- and the other `?0 := false`.
          -- The types may be both `D ?0`, which is the same
          -- but diverges in the different states.
          -- We do not check states for equality.
          --
          -- Of course, this is conservative and not maximally extensional.
          -- We might throw an ambiguity error too eagerly,
          -- but this can always be worked around.
          (Just{},  Just{})  -> return False
      inState st m = localTCState $ do putTC st; m

-- | @checkConstructorParameters c d pars@ checks that the data/record type
--   behind @c@ is has initial parameters (coming e.g. from a module instantiation)
--   that coincide with an prefix of @pars@.
checkConstructorParameters :: MonadTCM tcm => QName -> QName -> Args -> tcm ()
checkConstructorParameters c d pars = do
  dc <- liftTCM $ getConstructorData c
  checkParameters dc d pars

-- | Check that given parameters match the parameters of the inferred
--   constructor/projection.
checkParameters
  :: MonadTCM tcm
  => QName  -- ^ The record/data type name of the chosen constructor/projection.
  -> QName  -- ^ The record/data type name as supplied by the type signature.
  -> Args   -- ^ The parameters.
  -> tcm ()
checkParameters dc d pars = liftTCM $ do
  a  <- reduce (Def dc [])
  case a of
    Def d0 es -> do -- compare parameters
      let vs = fromMaybe __IMPOSSIBLE__ $ allApplyElims es
      reportSDoc "tc.lhs.split" 40 $ vcat $
        [ "checkParameters"
        , nest 2 $ "d                   =" <+> (text . prettyShow) d
        , nest 2 $ "d0 (should be == d) =" <+> (text . prettyShow) d0
        , nest 2 $ "dc                  =" <+> (text . prettyShow) dc
        , nest 2 $ "vs                  =" <+> prettyTCM vs
        , nest 2 $ "pars                =" <+> prettyTCM pars
        ]
      -- when (d0 /= d) __IMPOSSIBLE__ -- d could have extra qualification
      t <- typeOfConst d
      compareArgs [] [] t (Def d []) vs (take (length vs) pars)
    _ -> __IMPOSSIBLE__

checkSortOfSplitVar :: (MonadTCM m, PureTCM m, MonadError TCErr m,
                        LensSort a, PrettyTCM a, LensSort ty, PrettyTCM ty)
                    => DataOrRecord -> a -> Telescope -> Maybe ty -> m ()
checkSortOfSplitVar dr a tel mtarget = do
  liftTCM (reduce $ getSort a) >>= \case
    Type{} -> whenM isTwoLevelEnabled checkFibrantSplit
    Prop{} -> checkPropSplit
    SSet{} -> return ()
    Inf u _ -> when (univFibrancy u == IsFibrant) $ whenM isTwoLevelEnabled checkFibrantSplit
    sa      -> softTypeError =<< do
      liftTCM $ SortOfSplitVarError <$> isBlocked sa <*> sep
        [ "Cannot split on datatype in sort" , prettyTCM (getSort a) ]

  where
    checkPropSplit
      | IsRecord InductionAndEta { recordInduction=Nothing } <- dr = return ()
      | Just target <- mtarget = do
        reportSDoc "tc.sort.check" 20 $ "target prop:" <+> prettyTCM target
        checkIsProp target
      | otherwise              = do
          reportSDoc "tc.sort.check" 20 $ "no target prop"
          splitOnPropError dr

    checkIsProp t = runBlocked (isPropM t) >>= \case
      Left b      -> splitOnPropError dr -- TODO
      Right False -> splitOnPropError dr
      Right True  -> return ()

    checkFibrantSplit
      | IsRecord _ <- dr       = return ()
      | Just target <- mtarget = do
          reportSDoc "tc.sort.check" 20 $ "target:" <+> prettyTCM target
          checkIsFibrant target
          forM_ (telToList tel) $ \ d -> do
            let ty = snd $ unDom d
            checkIsCoFibrant ty
      | otherwise              = do
          reportSDoc "tc.sort.check" 20 $ "no target"
          splitOnFibrantError Nothing

    -- Cofibrant types are those that could be the domain of a fibrant
    -- pi type. (Notion by C. Sattler).
    checkIsCoFibrant t = runBlocked (isCoFibrantSort t) >>= \case
      Left b      -> splitOnFibrantError' t $ Just b
      Right False -> unlessM (isInterval t) $
                       splitOnFibrantError' t $ Nothing
      Right True  -> return ()

    checkIsFibrant t = runBlocked (isFibrant t) >>= \case
      Left b      -> splitOnFibrantError $ Just b
      Right False -> splitOnFibrantError Nothing
      Right True  -> return ()

    splitOnPropError dr = softTypeError $ SplitInProp dr

    splitOnFibrantError' t mb = softTypeError =<< do
      liftTCM $ SortOfSplitVarError mb <$> fsep
        [ "Cannot eliminate fibrant type" , prettyTCM a
        , "unless context type", prettyTCM t, "is also fibrant."
        ]

    splitOnFibrantError mb = softTypeError =<< do
      liftTCM $ SortOfSplitVarError mb <$> fsep
        [ "Cannot eliminate fibrant type" , prettyTCM a
        , "unless target type is also fibrant"
        ]
