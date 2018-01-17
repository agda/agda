{-# LANGUAGE CPP                  #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE NondecreasingIndentation #-}

module Agda.TypeChecking.Rules.LHS
  ( checkLeftHandSide
  , LHSResult(..)
  , bindAsPatterns
  , IsFlexiblePattern(..)
  ) where

#if MIN_VERSION_base(4,11,0)
import Prelude hiding ( (<>), mapM, null, sequence )
#else
import Prelude hiding ( mapM, null, sequence )
#endif

import Data.Maybe

import Control.Applicative hiding (empty)
import Control.Arrow (first, second, (***), left, right)
import Control.Monad
import Control.Monad.Plus (mfold)
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Writer hiding ((<>))
import Control.Monad.Trans.Maybe

import Data.Either (partitionEithers)
import Data.Function (on)
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.List (delete, sortBy, stripPrefix, (\\))
import qualified Data.List as List
import Data.Monoid ( Monoid, mempty, mappend )
import Data.Semigroup ( Semigroup )
import qualified Data.Semigroup as Semigroup
import Data.Traversable
import Data.Map (Map)
import qualified Data.Map as Map

import Agda.Interaction.Highlighting.Generate (storeDisambiguatedName)
import Agda.Interaction.Options
import Agda.Interaction.Options.Lenses

import Agda.Syntax.Internal as I
import Agda.Syntax.Internal.Pattern
import Agda.Syntax.Abstract (IsProjP(..))
import qualified Agda.Syntax.Abstract as A
import qualified Agda.Syntax.Abstract.Pattern as A
import Agda.Syntax.Abstract.Views (asView, deepUnscope)
import Agda.Syntax.Common as Common
import Agda.Syntax.Info as A
import Agda.Syntax.Literal
import Agda.Syntax.Position
import Agda.Syntax.Scope.Base (ScopeInfo, emptyScopeInfo)


import Agda.TypeChecking.Monad
import Agda.TypeChecking.Monad.Builtin (litType, constructorForm)

import qualified Agda.TypeChecking.Monad.Benchmark as Bench
import Agda.TypeChecking.Conversion
import Agda.TypeChecking.Constraints
import Agda.TypeChecking.Datatypes hiding (isDataOrRecordType)
import Agda.TypeChecking.Errors (dropTopLevelModule)
import Agda.TypeChecking.Irrelevance
import {-# SOURCE #-} Agda.TypeChecking.Empty
import Agda.TypeChecking.Forcing
import Agda.TypeChecking.Patterns.Abstract
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Records hiding (getRecordConstructor)
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Rewriting
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope

import {-# SOURCE #-} Agda.TypeChecking.Rules.Term (checkExpr)
import Agda.TypeChecking.Rules.LHS.Problem
import Agda.TypeChecking.Rules.LHS.ProblemRest
import Agda.TypeChecking.Rules.LHS.Unify
import Agda.TypeChecking.Rules.LHS.Implicit
import Agda.TypeChecking.Rules.Data

import Agda.Utils.Either
import Agda.Utils.Except (MonadError(..), ExceptT, runExceptT)
import Agda.Utils.Function
import Agda.Utils.Functor
import Agda.Utils.Lens
import Agda.Utils.List
import Agda.Utils.ListT
import Agda.Utils.Maybe
import Agda.Utils.Monad
import Agda.Utils.NonemptyList
import Agda.Utils.Null
import Agda.Utils.Permutation
import Agda.Utils.Pretty (prettyShow)
import Agda.Utils.Singleton
import Agda.Utils.Size

#include "undefined.h"
import Agda.Utils.Impossible

-- | Compute the set of flexible patterns in a list of patterns. The result is
--   the deBruijn indices of the flexible patterns.
flexiblePatterns :: [NamedArg A.Pattern] -> TCM FlexibleVars
flexiblePatterns nps = do
  forMaybeM (zip (downFrom $ length nps) nps) $ \ (i, Arg ai p) -> do
    runMaybeT $ (\ f -> FlexibleVar (getHiding ai) (getOrigin ai) f (Just i) i) <$> maybeFlexiblePattern p

-- | A pattern is flexible if it is dotted or implicit, or a record pattern
--   with only flexible subpatterns.
class IsFlexiblePattern a where
  maybeFlexiblePattern :: a -> MaybeT TCM FlexibleVarKind

  isFlexiblePattern :: a -> TCM Bool
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
    reportSDoc "tc.lhs.flex" 30 $ text "maybeFlexiblePattern" <+> prettyA p
    reportSDoc "tc.lhs.flex" 60 $ text "maybeFlexiblePattern (raw) " <+> (text . show . deepUnscope) p
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
        | Just PatOSystem <- conPRecord i -> return ImplicitFlex  -- expanded from ImplicitP
        | Just _          <- conPRecord i -> maybeFlexiblePattern ps
        | otherwise -> mzero
      I.VarP{}  -> mzero
      I.LitP{}  -> mzero
      I.ProjP{} -> mzero

-- | Lists of flexible patterns are 'RecordFlex'.
instance IsFlexiblePattern a => IsFlexiblePattern [a] where
  maybeFlexiblePattern ps = RecordFlex <$> mapM maybeFlexiblePattern ps

instance IsFlexiblePattern a => IsFlexiblePattern (Arg a) where
  maybeFlexiblePattern = maybeFlexiblePattern . unArg

instance IsFlexiblePattern a => IsFlexiblePattern (Common.Named name a) where
  maybeFlexiblePattern = maybeFlexiblePattern . namedThing

-- | Update the user patterns in the given problem, simplifying equations
--   between constructors where possible.
updateProblemEqs
 :: [ProblemEq] -> TCM [ProblemEq]
updateProblemEqs eqs = do
  reportSDoc "tc.lhs.top" 20 $ vcat
    [ text "updateProblem: equations to update"
    , nest 2 (vcat $ map prettyTCM eqs)
    ]

  eqs' <- updates eqs

  reportSDoc "tc.lhs.top" 20 $ vcat
    [ text "updateProblem: new equations"
    , nest 2 (vcat $ map prettyTCM eqs')
    ]

  return eqs'

  where

    updates :: [ProblemEq] -> TCM [ProblemEq]
    updates = concat <.> traverse update

    update :: ProblemEq -> TCM [ProblemEq]
    update eq@(ProblemEq p v a) = reduce v >>= constructorForm >>= \case
      Con c ci vs -> do
        -- we should only simplify equations between fully applied constructors
        contype <- getFullyAppliedConType c =<< reduce (unDom a)
        caseMaybe contype (return [eq]) $ \((d,_,pars),b) -> do
        TelV ctel _ <- telView b
        let bs = instTel ctel (map unArg vs)

        p <- expandLitPattern p
        case p of
          A.AsP info x p' ->
            (ProblemEq (A.VarP x) v a :) <$> update (ProblemEq p' v a)
          A.ConP cpi ambC ps -> do
            (c',_) <- disambiguateConstructor ambC d pars
            unless (conName c == conName c') {-'-} __IMPOSSIBLE__

            -- Insert implicit patterns
            ps <- insertImplicitPatterns ExpandLast ps ctel
            reportSDoc "tc.lhs.imp" 20 $
              text "insertImplicitPatternsT returned" <+> fsep (map prettyA ps)

            unless (length ps == length vs) $
              typeError $ WrongNumberOfConstructorArguments (conName c) (length vs) (length ps)

            updates $ zipWith3 ProblemEq (map namedArg ps) (map unArg vs) bs

          A.RecP pi fs -> do
            axs <- recordFieldNames . theDef <$> getConstInfo d
            -- In fs omitted explicit fields are replaced by underscores,
            -- and the fields are put in the correct order.
            ps <- insertMissingFields d (const $ A.WildP patNoRange) fs axs

            -- We also need to insert missing implicit or instance fields.
            ps <- insertImplicitPatterns ExpandLast ps ctel

            let eqs = zipWith3 ProblemEq (map namedArg ps) (map unArg vs) bs
            updates eqs

          _ -> return [eq]

      Lit l | A.LitP l' <- p , l == l' -> return []

      _ | A.WildP{} <- p -> return []

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
    all (isSolved . snd . asView) $
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
    -- impossible:
    isSolved A.ProjP{}       = __IMPOSSIBLE__
    isSolved A.DefP{}        = __IMPOSSIBLE__
    isSolved A.AsP{}         = __IMPOSSIBLE__  -- removed by asView
    isSolved A.PatternSynP{} = __IMPOSSIBLE__  -- expanded before
    isSolved A.WithP{}       = __IMPOSSIBLE__

-- | For each user-defined pattern variable in the 'Problem', check
-- that the corresponding data type (if any) does not contain a
-- constructor of the same name (which is not in scope); this
-- \"shadowing\" could indicate an error, and is not allowed.
--
-- Precondition: The problem has to be solved.

noShadowingOfConstructors
  :: Call -- ^ Trace, e.g., @CheckPatternShadowing clause@
  -> [ProblemEq] -> TCM ()
noShadowingOfConstructors mkCall eqs =
  traceCall mkCall $ mapM_ noShadowing eqs
  where
  noShadowing (ProblemEq p _ (Dom info (El _ a))) = case snd $ asView p of
   A.WildP       {} -> return ()
   A.AbsurdP     {} -> return ()
   A.DotP        {} -> return ()
   A.ConP        {} -> __IMPOSSIBLE__
   A.RecP        {} -> __IMPOSSIBLE__
   A.ProjP       {} -> __IMPOSSIBLE__
   A.DefP        {} -> __IMPOSSIBLE__
   A.AsP         {} -> __IMPOSSIBLE__ -- removed by asView
   A.LitP        {} -> __IMPOSSIBLE__
   A.PatternSynP {} -> __IMPOSSIBLE__
   A.WithP       {} -> __IMPOSSIBLE__
   -- Andreas, 2017-12-01, issue #2859.
   -- Due to parameter refinement, there can be (invisible) variable patterns from module
   -- parameters that shadow constructors.
   -- Thus, only complain about user written variable that shadow constructors.
   A.VarP x -> when (getOrigin info == UserWritten) $ do
    reportSDoc "tc.lhs.shadow" 30 $ vcat
      [ text $ "checking whether pattern variable " ++ prettyShow x ++ " shadows a constructor"
      , nest 2 $ text "type of variable =" <+> prettyTCM a
      , nest 2 $ text "position of variable =" <+> (text . show) (getRange x)
      ]
    reportSDoc "tc.lhs.shadow" 70 $ nest 2 $ text "a =" <+> pretty a
    a <- reduce a
    case ignoreSharing a of
      Def t _ -> do
        d <- theDef <$> getConstInfo t
        case d of
          Datatype { dataCons = cs } -> do
            case filter ((A.nameConcrete x ==) . A.nameConcrete . A.qnameName) cs of
              []      -> return ()
              (c : _) -> setCurrentRange x $
                typeError $ PatternShadowsConstructor x c
          AbstractDefn{} -> return ()
            -- Abstract constructors cannot be brought into scope,
            -- even by a bigger import list.
            -- Thus, they cannot be confused with variables.
            -- Alternatively, we could do getConstInfo in ignoreAbstractMode,
            -- then Agda would complain if a variable shadowed an abstract constructor.
          Axiom       {} -> return ()
          Function    {} -> return ()
          Record      {} -> return ()
          Constructor {} -> __IMPOSSIBLE__
          -- TODO: in the future some stuck primitives might allow constructors
          Primitive   {} -> return ()
      Var   {} -> return ()
      Pi    {} -> return ()
      Sort  {} -> return ()
      MetaV {} -> return ()
      -- TODO: If the type is a meta-variable, should the test be
      -- postponed? If there is a problem, then it will be caught when
      -- the completed module is type checked, so it is safe to skip
      -- the test here. However, users may be annoyed if they get an
      -- error in code which has already passed the type checker.
      Lam   {} -> __IMPOSSIBLE__
      Lit   {} -> __IMPOSSIBLE__
      Level {} -> __IMPOSSIBLE__
      Con   {} -> __IMPOSSIBLE__
      Shared{} -> __IMPOSSIBLE__
      DontCare{} -> __IMPOSSIBLE__

-- | Check that a dot pattern matches it's instantiation.
checkDotPattern :: DotPattern -> TCM ()
checkDotPattern (Dot e v (Dom info a)) =
  traceCall (CheckDotPattern e v) $ do
  reportSDoc "tc.lhs.dot" 15 $
    sep [ text "checking dot pattern"
        , nest 2 $ prettyA e
        , nest 2 $ text "=" <+> prettyTCM v
        , nest 2 $ text ":" <+> prettyTCM a
        ]
  applyRelevanceToContext (getRelevance info) $ do
    u <- checkExpr e a
    reportSDoc "tc.lhs.dot" 50 $
      sep [ text "equalTerm"
          , nest 2 $ pretty a
          , nest 2 $ pretty u
          , nest 2 $ pretty v
          ]
    -- Should be ok to do noConstraints here
    noConstraints $ equalTerm a u v

checkAbsurdPattern :: AbsurdPattern -> TCM ()
checkAbsurdPattern (Absurd r a) = isEmptyType r a

data LeftoverPatterns = LeftoverPatterns
  { patternVariables :: IntMap [A.Name]
  , asPatterns       :: [AsBinding]
  , dotPatterns      :: [DotPattern]
  , absurdPatterns   :: [AbsurdPattern]
  }

instance Semigroup LeftoverPatterns where
  x <> y = LeftoverPatterns
    { patternVariables = IntMap.unionWith (++) (patternVariables x) (patternVariables y)
    , asPatterns       = asPatterns x ++ asPatterns y
    , dotPatterns      = dotPatterns x ++ dotPatterns y
    , absurdPatterns   = absurdPatterns x ++ absurdPatterns y
    }

instance Monoid LeftoverPatterns where
  mempty  = LeftoverPatterns empty [] [] []
  mappend = (Semigroup.<>)

-- | Classify remaining patterns after splitting is complete into pattern
--   variables, as patterns, dot patterns, and absurd patterns.
--   Precondition: there are no more constructor patterns.
getLeftoverPatterns :: [ProblemEq] -> TCM LeftoverPatterns
getLeftoverPatterns eqs = do
  reportSDoc "tc.lhs.top" 30 $ text "classifying leftover patterns"
  mconcat <$> mapM getLeftoverPattern eqs
  where
    patternVariable x i  = LeftoverPatterns (singleton (i,[x])) [] [] []
    asPattern x v a      = LeftoverPatterns empty [AsB x v (unDom a)] [] []
    dotPattern e v a     = LeftoverPatterns empty [] [Dot e v a] []
    absurdPattern info a = LeftoverPatterns empty [] [] [Absurd info a]

    getLeftoverPattern :: ProblemEq -> TCM LeftoverPatterns
    getLeftoverPattern (ProblemEq p v a) = case p of
      (A.VarP x)        -> isEtaVar v (unDom a) >>= \case
        Just i  -> return $ patternVariable x i
        Nothing -> return $ asPattern x v a
      (A.WildP _)       -> return mempty
      (A.AsP info x p)  -> (asPattern x v a `mappend`) <$> do
        getLeftoverPattern $ ProblemEq p v a
      (A.DotP info e)   -> return $ dotPattern e v a
      (A.AbsurdP info)  -> return $ absurdPattern (getRange info) (unDom a)

      A.ConP{}        -> __IMPOSSIBLE__
      A.ProjP{}       -> __IMPOSSIBLE__
      A.DefP{}        -> __IMPOSSIBLE__
      A.LitP{}        -> __IMPOSSIBLE__
      A.PatternSynP{} -> __IMPOSSIBLE__
      A.RecP{}        -> __IMPOSSIBLE__
      A.WithP{}       -> __IMPOSSIBLE__

-- | Build a renaming for the internal patterns using variable names from
--   the user patterns. If there are multiple user names for the same internal
--   variable, the unused ones are returned as as-bindings.
getUserVariableNames :: Telescope -> IntMap [A.Name]
                     -> ([Maybe A.Name], [AsBinding])
getUserVariableNames tel names = runWriter $
  zipWithM makeVar (flattenTel tel) (downFrom $ size tel)

  where
    makeVar :: Dom Type -> Int -> Writer [AsBinding] (Maybe A.Name)
    makeVar a i | Just (x:xs) <- IntMap.lookup i names = do
      tell $ map (\y -> AsB y (var i) (unDom a)) xs
      return $ Just x
    makeVar a i = return Nothing

-- | After splitting is complete, we transfer the origins
--   We also transfer the locations of absurd patterns, since these haven't
--   been introduced yet in the internal pattern.
transferOrigins :: [NamedArg A.Pattern]
                -> [NamedArg DeBruijnPattern]
                -> TCM [NamedArg DeBruijnPattern]
transferOrigins ps qs = do
  reportSDoc "tc.lhs.origin" 40 $ vcat
    [ text "transferOrigins"
    , nest 2 $ vcat
      [ text "ps  =   " <+> prettyA ps
      , text "qs  =   " <+> pretty qs
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
          q' <- setOrigin (getOrigin p) <$>
                  (traverse $ traverse $ transfer $ namedArg p) q
          (q' :) <$> transfers ps qs
      | otherwise = (setOrigin Inserted q :) <$> transfers (p : ps) qs

    transfer :: A.Pattern -> DeBruijnPattern -> TCM DeBruijnPattern
    transfer p q = case (snd (asView p) , q) of

      (A.ConP pi _ ps , ConP c (ConPatternInfo mo mb l) qs) -> do
        let cpi = ConPatternInfo (mo $> PatOCon) mb l
        ConP c cpi <$> transfers ps qs

      (A.RecP pi fs , ConP c (ConPatternInfo mo mb l) qs) -> do
        let Def d _  = unEl $ unArg $ fromMaybe __IMPOSSIBLE__ mb
            axs = map (nameConcrete . qnameName) (conFields c) `withArgsFrom` qs
            cpi = ConPatternInfo (mo $> PatORec) mb l
        ps <- insertMissingFields d (const $ A.WildP patNoRange) fs axs
        ConP c cpi <$> transfers ps qs

      (p , ConP c (ConPatternInfo mo mb l) qs) -> do
        let cpi = ConPatternInfo (mo $> patOrigin p) mb l
        return $ ConP c cpi qs

      (p , VarP _ x) -> return $ VarP (patOrigin p) x

      (p , DotP _ u) -> return $ DotP (patOrigin p) u

      _ -> return q

    patOrigin :: A.Pattern -> PatOrigin
    patOrigin (A.VarP x)      = PatOVar x
    patOrigin A.DotP{}        = PatODot
    patOrigin A.ConP{}        = PatOCon
    patOrigin A.RecP{}        = PatORec
    patOrigin A.WildP{}       = PatOWild
    patOrigin A.AbsurdP{}     = PatOAbsurd
    patOrigin A.LitP{}        = PatOLit
    patOrigin A.AsP{}         = __IMPOSSIBLE__
    patOrigin A.ProjP{}       = __IMPOSSIBLE__
    patOrigin A.DefP{}        = __IMPOSSIBLE__
    patOrigin A.PatternSynP{} = __IMPOSSIBLE__
    patOrigin A.WithP{}       = __IMPOSSIBLE__

    matchingArgs :: NamedArg A.Pattern -> NamedArg DeBruijnPattern -> Bool
    matchingArgs p q
      -- The arguments match if
      -- 1. they are both projections,
      | isJust (A.maybePostfixProjP p) = isJust (isProjP q)
      -- 2. or they are both visible,
      | visible p && visible q = True
      -- 3. or they have the same hiding and the argument is not named,
      | sameHiding p q && isNothing (nameOf (unArg p)) = True
      -- 4. or they have the same hiding and the same name.
      | sameHiding p q && nameOf (unArg p) == nameOf (unArg q) = True
      -- Otherwise this argument was inserted by the typechecker.
      | otherwise = False


-- | If a user-written variable occurs more than once, it should be bound
--   to the same internal variable (or term) in all positions.
--   Returns the list of patterns with the duplicate user patterns removed.
checkPatternLinearity :: [ProblemEq] -> TCM [ProblemEq]
checkPatternLinearity eqs = do
  reportSDoc "tc.lhs.top" 30 $ text "Checking linearity of pattern variables"
  check Map.empty eqs
  where
    check _ [] = return []
    check vars (eq@(ProblemEq p u a) : eqs) = case p of
      A.VarP x | Just v <- Map.lookup x vars -> do
        noConstraints $ equalTerm (unDom a) u v
        check vars eqs
      A.VarP x | otherwise -> (eq:) <$> do
        check (Map.insert x u vars) eqs
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
      A.WithP{}       -> __IMPOSSIBLE__

      where continue = (eq:) <$> check vars eqs

-- | Bind the variables in a left hand side, making up hidden (dotted) names
--   for unnamed variables.
bindLHSVars :: [Maybe A.Name] -> Telescope -> TCM a -> TCM a
bindLHSVars []        tel@ExtendTel{}  _   = do
  reportSDoc "impossible" 10 $
    text "bindLHSVars: no patterns left, but tel =" <+> prettyTCM tel
  __IMPOSSIBLE__
bindLHSVars (_ : _)   EmptyTel         _   = __IMPOSSIBLE__
bindLHSVars []        EmptyTel         ret = ret
bindLHSVars (x : xs) tel0@(ExtendTel a tel) ret = do
  case x of
    Just x  -> addContext (x, a) $ bindLHSVars xs (absBody tel) ret
    Nothing -> bindDummy (absName tel)
               -- @bindDummy underscore@ does not fix issue 819, but
               -- introduces unwanted underscores in error messages
               -- (Andreas, 2015-05-28)
  where
    bindDummy s = do
      x <- if isUnderscore s then freshNoName_ else unshadowName =<< freshName_ ("." ++ argNameToString s)
      addContext (x, a) $ bindLHSVars xs (absBody tel) ret

-- | Bind as patterns
bindAsPatterns :: [AsBinding] -> TCM a -> TCM a
bindAsPatterns []                ret = ret
bindAsPatterns (AsB x v a : asb) ret = do
  reportSDoc "tc.lhs.as" 10 $ text "as pattern" <+> prettyTCM x <+>
    sep [ text ":" <+> prettyTCM a
        , text "=" <+> prettyTCM v
        ]
  addLetBinding defaultArgInfo x v a $ bindAsPatterns asb ret

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
  }

instance InstantiateFull LHSResult where
  instantiateFull' (LHSResult n tel ps abs t sub as) = LHSResult n
    <$> instantiateFull' tel
    <*> instantiateFull' ps
    <*> instantiateFull' abs
    <*> instantiateFull' t
    <*> instantiateFull' sub
    <*> instantiateFull' as

-- | Check a LHS. Main function.
--
--   @checkLeftHandSide a ps a ret@ checks that user patterns @ps@ eliminate
--   the type @a@ of the defined function, and calls continuation @ret@
--   if successful.

checkLeftHandSide :: forall a.
     Call
     -- ^ Trace, e.g. @CheckPatternShadowing clause@
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
checkLeftHandSide c f ps a withSub' strippedPats = Bench.billToCPS [Bench.Typing, Bench.CheckLHS] $ \ ret -> do

  -- To allow module parameters to be refined by matching, we're adding the
  -- context arguments as wildcard patterns and extending the type with the
  -- context telescope.
  cxt <- map (setOrigin Inserted) . reverse <$> getContext
  let tel = telFromList' prettyShow cxt
      cps = [ unnamed . A.VarP . fst <$> argFromDom d
            | d <- cxt ]
      eqs0 = zipWith3 ProblemEq (map namedArg cps) (map var $ downFrom $ size tel) (flattenTel tel)

  -- We need to grab all let-bindings here (while we still have the old
  -- context). They will be rebound below once we have the new context set up.
  -- Subtle: if we're checking a with the context will be empty so we can't use
  -- 'getOpen'. On the other hand, if we're checking a with the let bindings
  -- lives in the right context already so we can use 'openThing'.
  let openLet | isNothing withSub' = getOpen
              | otherwise          = return . openThing
  oldLets <- asks $ Map.toList . envLetBindings
  reportSDoc "tc.lhs.top" 70 $ vcat
    [ text "context =" <+> inTopContext (prettyTCM tel)
    , text "cIds    =" <+> (text . show =<< getContextId)
    , text "oldLets =" <+> text (show oldLets) ]
  oldLets <- sequence [ (x,) <$> openLet b | (x, b) <- oldLets ]

  let finalChecks :: LHSState a -> TCM a
      finalChecks (LHSState delta qs0 (Problem eqs rps _) b) = do

        unless (null rps) __IMPOSSIBLE__

        -- Update modalities of delta to match the modalities of the variables
        -- after the forcing translation. We can't perform the forcing translation
        -- yet, since that would mess with with-clause stripping.
        delta <- forceTranslateTelescope delta qs0

        addContext delta $ do
          noShadowingOfConstructors c eqs
          noPatternMatchingOnCodata qs0

        -- Compute substitution from the out patterns @qs0@
        let notProj ProjP{} = False
            notProj _       = True
                        -- Note: This works because we can't change the number of
                        --       arguments in the lhs of a with-function relative to
                        --       the parent function.
            numPats   = length $ takeWhile (notProj . namedArg) qs0
            -- In the case of a non-with function the pattern substitution
            -- should be weakened by the number of non-parameter patterns to
            -- get the paramSub.
            withSub = fromMaybe (wkS (numPats - length cxt) idS) withSub'
            patSub   = (map (patternToTerm . namedArg) $ reverse $ take numPats qs0) ++# (EmptyS __IMPOSSIBLE__)
            paramSub = composeS patSub withSub

        eqs <- addContext delta $ checkPatternLinearity eqs

        LeftoverPatterns patVars asb0 dots absurds
          <- addContext delta $ getLeftoverPatterns eqs

        -- Get the user-written names for the pattern variables
        let (vars, asb1) = getUserVariableNames delta patVars
            asb          = asb0 ++ asb1

        -- Rename internal patterns with these names
        let makeVar     = maybe deBruijnVar $ debruijnNamedVar . nameToArgName
            ren         = parallelS $ zipWith makeVar (reverse vars) [0..]

        qs <- transferOrigins (cps ++ ps) $ applySubst ren qs0

        let hasAbsurd = not . null $ absurds

        let lhsResult = LHSResult (length cxt) delta qs hasAbsurd b patSub asb
            newLets = [ AsB x (applySubst paramSub v) (applySubst paramSub $ unDom a) | (x, (v, a)) <- oldLets ]

        -- Debug output
        reportSDoc "tc.lhs.top" 10 $
          vcat [ text "checked lhs:"
               , nest 2 $ vcat
                 [ text "delta   = " <+> prettyTCM delta
                 , text "dots    = " <+> addContext delta (brackets $ fsep $ punctuate comma $ map prettyTCM dots)
                 , text "asb     = " <+> addContext delta (brackets $ fsep $ punctuate comma $ map prettyTCM asb)
                 , text "absurds = " <+> addContext delta (brackets $ fsep $ punctuate comma $ map prettyTCM absurds)
                 , text "qs      = " <+> addContext delta (prettyList $ map pretty qs)
                 ]
               ]
        reportSDoc "tc.lhs.top" 30 $
          nest 2 $ vcat
                 [ text "vars   = " <+> text (show vars)
                 ]
        reportSDoc "tc.lhs.top" 20 $ nest 2 $ text "patSub   = " <+> pretty patSub
        reportSDoc "tc.lhs.top" 20 $ nest 2 $ text "withSub  = " <+> pretty withSub
        reportSDoc "tc.lhs.top" 20 $ nest 2 $ text "paramSub = " <+> pretty paramSub
        reportSDoc "tc.lhs.top" 50 $ text "old let-bindings:" <+> text (show oldLets)
        reportSDoc "tc.lhs.top" 50 $ text "new let-bindings:" <+> (brackets $ fsep $ punctuate comma $ map prettyTCM newLets)

        bindLHSVars vars delta $ do

          reportSDoc "tc.lhs.top" 10 $ text "bound pattern variables"
          reportSDoc "tc.lhs.top" 60 $ nest 2 $ text "context = " <+> (pretty =<< getContextTelescope)
          reportSDoc "tc.lhs.top" 10 $ nest 2 $ text "type  = " <+> prettyTCM b
          reportSDoc "tc.lhs.top" 60 $ nest 2 $ text "type  = " <+> pretty b

          bindAsPatterns newLets $

            -- At this point we need to update the module parameters for all
            -- parent modules.
            applyRelevanceToContext (getRelevance b) $ updateModuleParameters paramSub $ do
            bindAsPatterns asb $ do

              -- Check dot patterns
              mapM_ checkDotPattern dots
              mapM_ checkAbsurdPattern absurds

            -- Issue2303: don't bind asb' for the continuation (return in lhsResult instead)
            ret lhsResult

  st0 <- initLHSState tel eqs0 ps a finalChecks

  -- after we have introduced variables, we can add the patterns stripped by
  -- with-desugaring to the state.
  let withSub = fromMaybe __IMPOSSIBLE__ withSub'
  withEqs <- updateProblemEqs $ applySubst withSub strippedPats
  let st = over (lhsProblem . problemEqs) (++ withEqs) st0

  -- doing the splits:
  (result, block) <- inTopContext $ runWriterT $ checkLHS f st
  return result

-- | Determine in which order the splits should be tried by
--   reordering/inserting/dropping the problem equations.
splitStrategy :: [ProblemEq] -> [ProblemEq]
splitStrategy = filter shouldSplit
  where
    shouldSplit :: ProblemEq -> Bool
    shouldSplit (ProblemEq p v a) = case snd $ asView p of
      A.LitP{}    -> True
      A.RecP{}    -> True
      A.ConP{}    -> True

      A.VarP{}    -> False
      A.WildP{}   -> False
      A.DotP{}    -> False
      A.AbsurdP{} -> False

      A.ProjP{}       -> __IMPOSSIBLE__
      A.DefP{}        -> __IMPOSSIBLE__
      A.AsP{}         -> __IMPOSSIBLE__
      A.PatternSynP{} -> __IMPOSSIBLE__
      A.WithP{}       -> __IMPOSSIBLE__


-- | The loop (tail-recursive): split at a variable in the problem until problem is solved
checkLHS
  :: forall tcm a. (MonadTCM tcm, MonadWriter Blocked_ tcm, HasConstInfo tcm, MonadError TCErr tcm, MonadDebug tcm)
  => Maybe QName      -- ^ The name of the definition we are checking.
  -> LHSState a       -- ^ The current state.
  -> tcm a
checkLHS mf st@(LHSState tel ip problem target) = do
  if isSolvedProblem problem then
    liftTCM $ (problem ^. problemCont) st
  else do
    unlessM (optPatternMatching <$> gets getPragmaOptions) $
      unless (problemAllVariables problem) $
        typeError $ GenericError $ "Pattern matching is disabled"

    let splitsToTry = splitStrategy $ problem ^. problemEqs

    foldr trySplit trySplitRest splitsToTry >>= \case
      Right st' -> do
        -- If the new target type is irrelevant, we need to continue in irr. cxt.
        -- (see Issue 939).
        let rel = getRelevance $ st' ^. lhsTarget
        applyRelevanceToContext rel $ checkLHS mf st'

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
    splitArg (ProblemEq p v (Dom _ a)) = traceCall (CheckPattern p tel a) $ do

      reportSDoc "tc.lhs.split" 30 $ sep
        [ text "split looking at pattern"
        , nest 2 $ text "p =" <+> prettyA p
        ]

      -- in order to split, v must be a variable.
      i <- liftTCM $ addContext tel $ ifJustM (isEtaVar v a) return $
             softTypeError $ SplitOnNonVariable v a

      let pos = size tel - (i+1)
          (delta1, tel'@(ExtendTel dom adelta2)) = splitTelescopeAt pos tel

      p <- liftTCM $ expandLitPattern p
      case snd $ asView p of
        (A.LitP l)        -> splitLit delta1 dom adelta2 l
        p@A.RecP{}        -> splitCon delta1 dom adelta2 p Nothing
        p@(A.ConP _ c ps) -> splitCon delta1 dom adelta2 p $ Just c

        A.VarP{}        -> __IMPOSSIBLE__
        A.WildP{}       -> __IMPOSSIBLE__
        A.DotP{}        -> __IMPOSSIBLE__
        A.AbsurdP{}     -> __IMPOSSIBLE__
        A.ProjP{}       -> __IMPOSSIBLE__
        A.DefP{}        -> __IMPOSSIBLE__
        A.AsP{}         -> __IMPOSSIBLE__
        A.PatternSynP{} -> __IMPOSSIBLE__
        A.WithP{}       -> __IMPOSSIBLE__


    splitRest :: NamedArg A.Pattern -> ExceptT TCErr tcm (LHSState a)
    splitRest p = setCurrentRange p $ do
      reportSDoc "tc.lhs.split" 20 $ sep
        [ text "splitting problem rest"
        , nest 2 $ text "projection pattern =" <+> prettyA p
        , nest 2 $ text "eliminates type    =" <+> prettyTCM target
        ]
      reportSDoc "tc.lhs.split" 80 $ sep
        [ nest 2 $ text $ "projection pattern (raw) = " ++ show p
        ]

      -- @p@ should be a projection pattern projection from @target@
      (orig, ambProjName) <- ifJust (A.maybePostfixProjP p) return $
        addContext tel $ softTypeError $ CannotEliminateWithPattern p (unArg target)

      (projName, projType) <- suspendErrors $
        addContext tel $ disambiguateProjection (getHiding p) ambProjName target

      -- Compute the new rest type by applying the projection type to 'self'.
      -- Note: we cannot be in a let binding.
      f <- ifJust mf return $ hardTypeError $
             GenericError "Cannot use copatterns in a let binding"
      let self = Def f $ patternsToElims ip
      target' <- traverse (`piApply1` self) projType

      -- Compute the new state
      let projP    = target' $> Named Nothing (ProjP orig projName)
          ip'      = ip ++ [projP]
          -- drop the projection pattern (already splitted)
          problem' = over problemRestPats tail problem
      liftTCM $ updateProblemRest (LHSState tel ip' problem' target')


    splitLit :: Telescope     -- ^ The types of arguments before the one we split on
             -> Dom Type      -- ^ The type of the literal we split on
             -> Abs Telescope -- ^ The types of arguments after the one we split on
             -> Literal       -- ^ The literal written by the user
             -> ExceptT TCErr tcm (LHSState a)
    splitLit delta1 dom@(Dom info a) adelta2 lit = do
      let delta2 = absApp adelta2 (Lit lit)
          delta' = abstract delta1 delta2
          rho    = singletonS (size delta2) (LitP lit)
          -- Andreas, 2015-06-13 Literals are closed, so no need to raise them!
          -- rho    = liftS (size delta2) $ singletonS 0 (Lit lit)
          -- rho    = [ var i | i <- [0..size delta2 - 1] ]
          --       ++ [ raise (size delta2) $ Lit lit ]
          --       ++ [ var i | i <- [size delta2 ..] ]
          eqs'     = applyPatSubst rho $ problem ^. problemEqs
          ip'      = applySubst rho ip
          target'  = applyPatSubst rho target

      -- Andreas, 2010-09-07 cannot split on irrelevant args
      when (unusableRelevance $ getRelevance info) $
        addContext delta1 $ hardTypeError $ SplitOnIrrelevant dom

      -- check that a is indeed the type of lit (otherwise fail softly)
      -- if not, fail softly since it could be instantiated by a later split.
      suspendErrors $ equalType a =<< litType lit

      -- Compute the new state
      eqs' <- liftTCM $ addContext delta' $ updateProblemEqs eqs'
      let problem' = set problemEqs eqs' problem
      liftTCM $ updateProblemRest (LHSState delta' ip' problem' target')


    splitCon :: Telescope     -- ^ The types of arguments before the one we split on
             -> Dom Type      -- ^ The type of the constructor we split on
             -> Abs Telescope -- ^ The types of arguments after the one we split on
             -> A.Pattern     -- ^ The pattern written by the user
             -> Maybe AmbiguousQName  -- ^ @Just c@ for a (possibly ambiguous) constructor @c@, or
                                      --   @Nothing@ for a record pattern
             -> ExceptT TCErr tcm (LHSState a)
    splitCon delta1 dom@(Dom info a) adelta2 focusPat ambC = do
      let delta2 = absBody adelta2

      reportSDoc "tc.lhs.split" 10 $ sep
        [ text "checking lhs"
        , nest 2 $ text "tel =" <+> prettyTCM tel
        , nest 2 $ text "rel =" <+> (text $ show $ getRelevance info)
        ]

      reportSDoc "tc.lhs.split" 15 $ sep
        [ text "split problem"
        , nest 2 $ vcat
          [ text "delta1 = " <+> prettyTCM delta1
          , text "a      = " <+> addContext delta1 (prettyTCM a)
          , text "delta2 = " <+> addContext delta1 (addContext ("x", dom) (prettyTCM delta2))
          ]
        ]

      -- We should be at a data/record type
      (d, pars, ixs) <- addContext delta1 $ isDataOrRecordType dom

      -- The constructor should construct an element of this datatype
      (c, b) <- liftTCM $ addContext delta1 $ case ambC of
        Just ambC -> disambiguateConstructor ambC d pars
        Nothing   -> getRecordConstructor d pars a

      -- The type of the constructor will end in an application of the datatype
      TelV gamma (El _ ctarget) <- liftTCM $ telView b
      let Def d' es' = ignoreSharing ctarget
          cixs = drop (size pars) $ fromMaybe __IMPOSSIBLE__ $ allApplyElims es'

      unless (d == d') {-'-} __IMPOSSIBLE__

      -- Get names for the constructor arguments from the user patterns
      gamma <- liftTCM $ case focusPat of
        A.ConP _ _ ps -> do
          ps <- insertImplicitPatterns ExpandLast ps gamma
          return $ useNamesFromPattern ps gamma
        A.RecP _ fs -> do
          axs <- recordFieldNames . theDef <$> getConstInfo d
          ps <- insertMissingFields d (const $ A.WildP patNoRange) fs axs
          ps <- insertImplicitPatterns ExpandLast ps gamma
          return $ useNamesFromPattern ps gamma
        _ -> __IMPOSSIBLE__

      -- Andreas 2010-09-07  propagate relevance info to new vars
      let updRel = composeRelevance (getRelevance info)
      gamma <- return $ mapRelevance updRel <$> gamma

      -- Get the type of the datatype.
      da <- (`piApply` pars) . defType <$> getConstInfo d
      reportSDoc "tc.lhs.split" 30 $ text "  da = " <+> prettyTCM da

      reportSDoc "tc.lhs.top" 15 $ addContext delta1 $
        sep [ text "preparing to unify"
            , nest 2 $ vcat
              [ text "c      =" <+> prettyTCM c <+> text ":" <+> prettyTCM b
              , text "d      =" <+> prettyTCM (Def d (map Apply pars)) <+> text ":" <+> prettyTCM da
              , text "gamma  =" <+> prettyTCM gamma
              , text "pars   =" <+> brackets (fsep $ punctuate comma $ map prettyTCM pars)
              , text "ixs    =" <+> brackets (fsep $ punctuate comma $ map prettyTCM ixs)
              , text "cixs   =" <+> addContext gamma (brackets (fsep $ punctuate comma $ map prettyTCM cixs))
              ]
            ]

      let delta1Gamma = delta1 `abstract` gamma
          da'  = raise (size gamma) da
          ixs' = raise (size gamma) ixs

      -- All variables are flexible.
      let flex = allFlexVars $ delta1Gamma

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
      --        Δ₁' ⊢ c ρ₂ : (D pars cixs)(ρ₁;ρ₂)
      -- We have
      --        cixs(ρ₁;ρ₂)
      --         ≡ cixs(ρ₀)   (since ρ₀=ρ₁;ρ₂)
      --         ≡ ixs(ρ₀)    (by unification)
      --         ≡ ixs(ρ₁)    (since ixs doesn't actually depend on Γ)
      -- so     Δ₁' ⊢ c ρ₂ : (D pars ixs)ρ₁
      -- Putting this together with ρ₁ gives ρ₃ = ρ₁;c ρ₂
      --        Δ₁' ⊢ ρ₁;c ρ₂ : Δ₁(x : D vs ws)
      -- and lifting over Δ₂ gives the final substitution ρ = ρ₃;Δ₂
      -- from Δ' = Δ₁';Δ₂ρ₃
      --        Δ' ⊢ ρ : Δ₁(x : D vs ws)Δ₂

      liftTCM (unifyIndices delta1Gamma flex da' cixs ixs') >>= \case

        -- Mismatch.  Report and abort.
        NoUnify neg -> hardTypeError $ ImpossibleConstructor (conName c) neg

        -- Unclear situation.  Try next split.
        DontKnow errs -> softTypeError $ SplitError $
          UnificationStuck (conName c) (delta1 `abstract` gamma) cixs ixs' errs

        -- Success.
        Unifies (delta1',rho0,es) -> do

          reportSDoc "tc.lhs.top" 15 $ text "unification successful"
          reportSDoc "tc.lhs.top" 20 $ nest 2 $ vcat
            [ text "delta1' =" <+> prettyTCM delta1'
            , text "rho0    =" <+> addContext delta1' (prettyTCM rho0)
            , text "es      =" <+> addContext delta1' (prettyTCM $ (fmap . fmap . fmap) patternToTerm es)
            ]

          -- split substitution into part for Δ₁ and part for Γ
          let (rho1,rho2) = splitS (size gamma) rho0

          reportSDoc "tc.lhs.top" 20 $ addContext delta1' $ nest 2 $ vcat
            [ text "rho1    =" <+> prettyTCM rho1
            , text "rho2    =" <+> prettyTCM rho2
            ]

          -- Andreas, 2010-09-09, save the type.
          -- It is relative to Δ₁, but it should be relative to Δ₁'
          let a' = applyPatSubst rho1 a
          -- Also remember if we are a record pattern.
          isRec <- isRecord d
          let cpi = ConPatternInfo { conPRecord = isRec $> PatOCon
                                   , conPType   = Just $ Arg info a'
                                   , conPLazy   = False }

          -- compute final context and substitution
          let crho2   = ConP c cpi $ applySubst rho2 $ teleNamedArgs gamma
              rho3    = consS crho2 rho1
              delta2' = applyPatSubst rho3 delta2
              delta'  = delta1' `abstract` delta2'
              rho     = liftS (size delta2) rho3

          reportSDoc "tc.lhs.top" 20 $ addContext delta1' $ nest 2 $ vcat
            [ text "crho2   =" <+> prettyTCM crho2
            , text "rho3    =" <+> prettyTCM rho3
            , text "delta2' =" <+> prettyTCM delta2'
            ]
          reportSDoc "tc.lhs.top" 70 $ addContext delta1' $ nest 2 $ vcat
            [ text "crho2   =" <+> pretty crho2
            , text "rho3    =" <+> pretty rho3
            , text "delta2' =" <+> pretty delta2'
            ]

          reportSDoc "tc.lhs.top" 15 $ nest 2 $ vcat
            [ text "delta'  =" <+> prettyTCM delta'
            , text "rho     =" <+> addContext delta' (prettyTCM rho)
            ]

          -- Compute the new out patterns and target type.
          let ip'      = applySubst rho ip
              target'  = applyPatSubst rho target

          -- Update the problem equations
          let eqs' = applyPatSubst rho $ problem ^. problemEqs
          eqs' <- liftTCM $ addContext delta' $ updateProblemEqs eqs'

          let problem' = set problemEqs eqs' problem

          -- if rest type reduces,
          -- extend the split problem by previously not considered patterns
          st' <- liftTCM $ updateProblemRest $ LHSState delta' ip' problem' target'

          reportSDoc "tc.lhs.top" 12 $ sep
            [ text "new problem from rest"
            , nest 2 $ vcat
              [ text "delta'  =" <+> prettyTCM (st' ^. lhsTel)
              , text "eqs'    =" <+> addContext (st' ^. lhsTel) (prettyTCM $ st' ^. lhsProblem ^. problemEqs)
              , text "ip'     =" <+> addContext (st' ^. lhsTel) (pretty $ st' ^. lhsOutPat)
              ]
            ]
          return st'




-- | Ensures that we are not performing pattern matching on codata.

noPatternMatchingOnCodata :: [NamedArg DeBruijnPattern] -> TCM ()
noPatternMatchingOnCodata = mapM_ (check . namedArg)
  where
  check (VarP {})   = return ()
  check (DotP {})   = return ()
  check (ProjP{})   = return ()
  check (LitP {})   = return ()  -- Literals are assumed not to be coinductive.
  check (ConP con _ ps) = do
    reportSDoc "tc.lhs.top" 40 $
      text "checking whether" <+> prettyTCM con <+> text "is a coinductive constructor"
    TelV _ t <- telView' . defType <$> do getConstInfo $ conName con
    c <- isCoinductive t
    case c of
      Nothing    -> __IMPOSSIBLE__
      Just False -> mapM_ (check . namedArg) ps
      Just True  -> typeError $
        GenericError "Pattern matching on coinductive types is not allowed"

-- | When working with a monad @m@ implementing @MonadTCM@ and @MonadError TCErr@,
--   @suspendErrors f@ performs the TCM action @f@ but catches any errors and throws
--   them in the monad @m@ instead.
suspendErrors :: (MonadTCM m, MonadError TCErr m) => TCM a -> m a
suspendErrors f = do
  ok <- liftTCM $ (Right <$> f) `catchError` (return . Left)
  either throwError return ok

-- | A more direct implementation of the specification
--   @softTypeError err == suspendErrors (typeError err)@
softTypeError :: (MonadTCM m, MonadError TCErr m) => TypeError -> m a
softTypeError err = throwError =<< typeError_ err

-- | A convenient alias for @liftTCM . typeError@. Throws the error directly
--   in the TCM even if there is a surrounding monad also implementing
--   @MonadError TCErr@.
hardTypeError :: (MonadTCM m) => TypeError -> m a
hardTypeError = liftTCM . typeError

-- | Check if the type is a data or record type and return its name,
--   definition, parameters, and indices. Fails softly if the type could become
--   a data/record type by instantiating a variable/metavariable, or fail hard
--   otherwise.
isDataOrRecordType :: (MonadTCM m, MonadDebug m)
                   => Dom Type -> ExceptT TCErr m (QName, Args, Args)
isDataOrRecordType dom@(Dom info a) = liftTCM (reduceB a) >>= \case
  NotBlocked ReallyNotBlocked a -> case ignoreSharing $ unEl a of

    -- Subcase: split type is a Def.
    Def d es -> (liftTCM $ theDef <$> getConstInfo d) >>= \case

      Datatype{dataPars = np} -> do
        -- We cannot split on (shape-)irrelevant non-records.
        -- Andreas, 2011-10-04 unless allowed by option
        reportSLn "tc.lhs.split" 30 $ "split ConP: relevance is " ++ show (getRelevance info)
        when (unusableRelevance $ getRelevance info) $
          unlessM (liftTCM $ optExperimentalIrrelevance <$> pragmaOptions) $
            hardTypeError $ SplitOnIrrelevant dom

        let (pars, ixs) = splitAt np $ fromMaybe __IMPOSSIBLE__ $ allApplyElims es
        return (d, pars, ixs)

      Record{} -> do
        let pars = fromMaybe __IMPOSSIBLE__ $ allApplyElims es
        return (d, pars, [])

      -- Issue #2253: the data type could be abstract.
      AbstractDefn{} -> hardTypeError . GenericDocError =<< do
        liftTCM $ text "Cannot split on abstract data type" <+> prettyTCM d

      -- the type could be an axiom
      Axiom{} -> hardTypeError =<< notData

      Function{}    -> __IMPOSSIBLE__
      Constructor{} -> __IMPOSSIBLE__
      Primitive{}   -> __IMPOSSIBLE__

    -- variable or metavariable: fail softly
    Var{}      -> softTypeError =<< notData
    MetaV{}    -> softTypeError =<< notData

    -- pi or sort: fail hard
    Pi{}       -> hardTypeError =<< notData
    Sort{}     -> hardTypeError =<< notData

    Lam{}      -> __IMPOSSIBLE__
    Lit{}      -> __IMPOSSIBLE__
    Con{}      -> __IMPOSSIBLE__
    Level{}    -> __IMPOSSIBLE__
    DontCare{} -> __IMPOSSIBLE__
    Shared{}   -> __IMPOSSIBLE__

  -- Type is blocked on a meta or something else: fail softly
  _ -> softTypeError =<< notData

  where notData = liftTCM $ SplitError . NotADatatype <$> buildClosure a


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
  :: Hiding         -- ^ Hiding info of the projection's principal argument.
  -> AmbiguousQName -- ^ Name of the projection to be disambiguated.
  -> Arg Type       -- ^ Record type we are projecting from.
  -> TCM (QName, Arg Type)
disambiguateProjection h ambD@(AmbQ ds) b = do
  -- If the target is not a record type, that's an error.
  -- It could be a meta, but since we cannot postpone lhs checking, we crash here.
  caseMaybeM (liftTCM $ isRecordType $ unArg b) notRecord $ \(r, vs, def) -> case def of
    Record{ recFields = fs } -> do
      reportSDoc "tc.lhs.split" 20 $ sep
        [ text $ "we are of record type r  = " ++ prettyShow r
        , text   "applied to parameters vs = " <+> prettyTCM vs
        , text $ "and have fields       fs = " ++ prettyShow fs
        ]
      -- Try the projection candidates.
      -- Note that tryProj wraps TCM in an ExceptT, collecting errors
      -- instead of throwing them to the user immediately.
      -- First, we try to find a disambiguation that doesn't produce
      -- any new constraints.
      disambiguations <- mapM (runExceptT . tryProj False fs r vs) ds
      case partitionEithers $ toList disambiguations of
        (_ , (d,a):_) -> do
          -- From here, we have the correctly disambiguated projection.
          -- For highlighting, we remember which name we disambiguated to.
          -- This is safe here (fingers crossed) as we won't decide on a
          -- different projection even if we backtrack and come here again.
          liftTCM $ storeDisambiguatedName d
          return (d,a)
        (_ , []     ) -> do
          -- If this fails, we try again with constraints, but we require
          -- the solution to be unique.
          disambiguations <- mapM (runExceptT . tryProj True fs r vs) ds
          case partitionEithers $ toList disambiguations of
            ([]   , []      ) -> __IMPOSSIBLE__
            (err:_, []      ) -> throwError err
            (errs , [(d,a)]) -> do
              liftTCM $ storeDisambiguatedName d
              return (d,a)
            (errs , disambs@((d,a):_)) -> typeError . GenericDocError =<< vcat
              [ text "Ambiguous projection " <> prettyTCM (qnameName d) <> text "."
              , text "It could refer to any of"
              , nest 2 $ vcat $ map showDisamb disambs
              ]
    _ -> __IMPOSSIBLE__

  where
    showDisamb (d,_) =
      let r = head $ filter (noRange /=) $ map nameBindingSite $ reverse $ mnameToList $ qnameModule d
      in  (pretty =<< dropTopLevelModule d) <+> text "(introduced at " <> prettyTCM r <> text ")"

    notRecord = wrongProj $ headNe ds

    wrongProj :: (MonadTCM m, MonadError TCErr m) => QName -> m a
    wrongProj d = softTypeError =<< do
      liftTCM $ GenericDocError <$> sep
        [ text "Cannot eliminate type "
        , prettyTCM (unArg b)
        , text " with projection "
        , if isAmbiguous ambD then
            text . prettyShow =<< dropTopLevelModule d
          else
            prettyTCM d
        ]

    wrongHiding :: (MonadTCM m, MonadError TCErr m) => QName -> m a
    wrongHiding d = softTypeError =<< do
      liftTCM $ GenericDocError <$> sep
        [ text "Wrong hiding used for projection " , prettyTCM d ]

    tryProj
      :: Bool                 -- ^ Are we allowed to create new constraints?
      -> [Arg QName]          -- ^ Fields of record type under consideration.
      -> QName                -- ^ Name of record type we are eliminating.
      -> Args                 -- ^ Parameters of record type we are eliminating.
      -> QName                -- ^ Candidate projection.
      -> ExceptT TCErr TCM (QName, Arg Type)
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
        argd <- maybe (wrongProj d) return $ List.find ((d ==) . unArg) fs

        let ai = setRelevance (getRelevance argd) $ projArgInfo proj

        -- Andreas, 2016-12-31, issue #2374:
        -- We can also disambiguate by hiding info.
        unless (sameHiding h ai) $ wrongHiding d

        -- Andreas, 2016-12-31, issue #1976: Check parameters.
        suspendErrors $ applyUnless constraintsOk noConstraints $
          checkParameters qr r vs

        -- Get the type of projection d applied to "self"
        dType <- liftTCM $ defType <$> getConstInfo d  -- full type!
        reportSDoc "tc.lhs.split" 20 $ sep
          [ text "we are being projected by dType = " <+> prettyTCM dType
          ]
        projType <- liftTCM $ dType `piApplyM` vs
        return (d0 , Arg ai projType)

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

  disambiguations <- mapM (runExceptT . tryCon False cons d pars) cs -- TODO: be more lazy
  case partitionEithers $ toList disambiguations of
    (_ , (c0,c,a):_) -> do
      -- If constructor pattern was ambiguous,
      -- remember our choice for highlighting info.
      when (isAmbiguous ambC) $ liftTCM $ storeDisambiguatedName c0
      return (c,a)
    (_ , []     ) -> do
      disambiguations <- mapM (runExceptT . tryCon True cons d pars) cs
      case partitionEithers $ toList disambiguations of
        ([]   , []        ) -> __IMPOSSIBLE__
        (err:_, []        ) -> throwError err
        (errs , [(c0,c,a)]) -> do
          when (isAmbiguous ambC) $ liftTCM $ storeDisambiguatedName c0
          return (c,a)

        (errs , disambs@((c0,c,a):_)) -> typeError . GenericDocError =<< vcat
          [ text "Ambiguous constructor " <> prettyTCM (qnameName $ conName c) <> text "."
          , text "It could refer to any of"
          , nest 2 $ vcat $ map showDisamb disambs
          ]

  where
    showDisamb (c0,_,_) =
      let r = head $ filter (noRange /=) $ map nameBindingSite $ reverse $ mnameToList $ qnameModule c0
      in  (pretty =<< dropTopLevelModule c0) <+> text "(introduced at " <> prettyTCM r <> text ")"

    abstractConstructor c = softTypeError $
      AbstractConstructorNotInScope c

    wrongDatatype c d = softTypeError $
      ConstructorPatternInWrongDatatype c d

    tryCon
      :: Bool        -- ^ Are we allowed to create new constraints?
      -> [QName]     -- ^ Constructors of data type under consideration.
      -> QName       -- ^ Name of data/record type we are eliminating.
      -> Args        -- ^ Parameters of data/record type we are eliminating.
      -> QName       -- ^ Candidate constructor.
      -> ExceptT TCErr TCM (QName, ConHead, Type)
    tryCon constraintsOk cons d pars c = getConstInfo' c >>= \case
      Left (SigUnknown err) -> __IMPOSSIBLE__
      Left SigAbstract -> abstractConstructor c
      Right def -> do
        let con = conSrcCon $ theDef def
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
        suspendErrors $ applyUnless constraintsOk noConstraints $
          checkConstructorParameters c d pars

        -- Get the type from the original constructor
        cType <- (`piApply` pars) . defType <$> getConInfo con

        return (c, con, cType)




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
  case ignoreSharing a of
    Def d0 es -> do -- compare parameters
      let vs = fromMaybe __IMPOSSIBLE__ $ allApplyElims es
      reportSDoc "tc.lhs.split" 40 $
        vcat [ nest 2 $ text "d                   =" <+> (text . prettyShow) d
             , nest 2 $ text "d0 (should be == d) =" <+> (text . prettyShow) d0
             , nest 2 $ text "dc                  =" <+> (text . prettyShow) dc
             , nest 2 $ text "vs                  =" <+> prettyTCM vs
             ]
      -- when (d0 /= d) __IMPOSSIBLE__ -- d could have extra qualification
      t <- typeOfConst d
      compareArgs [] [] t (Def d []) vs (take (length vs) pars)
    _ -> __IMPOSSIBLE__
