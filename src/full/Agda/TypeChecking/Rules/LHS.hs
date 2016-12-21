{-# LANGUAGE CPP                  #-}

module Agda.TypeChecking.Rules.LHS where

import Prelude hiding (mapM, sequence)

import Data.Maybe

import Control.Applicative
import Control.Arrow (first, second, (***))
import Control.Monad hiding (mapM, forM, sequence)
import Control.Monad.State hiding (mapM, forM, sequence)
import Control.Monad.Reader hiding (mapM, forM, sequence)
import Control.Monad.Trans.Maybe

import Data.Function (on)
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.List (delete, sortBy, stripPrefix)
import Data.Monoid
import Data.Traversable
import Data.Map (Map)
import qualified Data.Map as Map

import Agda.Interaction.Options
import Agda.Interaction.Options.Lenses

import Agda.Syntax.Internal as I
import Agda.Syntax.Internal.Pattern
import Agda.Syntax.Abstract (IsProjP(..))
import qualified Agda.Syntax.Abstract as A
import Agda.Syntax.Abstract.Views (asView)
import Agda.Syntax.Common as Common
import Agda.Syntax.Info as A
import Agda.Syntax.Position
import Agda.Syntax.Scope.Base (ScopeInfo, emptyScopeInfo)


import Agda.TypeChecking.Monad

import qualified Agda.TypeChecking.Monad.Benchmark as Bench
import Agda.TypeChecking.Conversion
import Agda.TypeChecking.Constraints
import Agda.TypeChecking.Datatypes
import Agda.TypeChecking.Irrelevance
import {-# SOURCE #-} Agda.TypeChecking.Empty
import Agda.TypeChecking.Patterns.Abstract
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Records
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Rewriting
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope

import {-# SOURCE #-} Agda.TypeChecking.Rules.Term (checkExpr)
import Agda.TypeChecking.Rules.LHS.AsPatterns
import Agda.TypeChecking.Rules.LHS.Problem hiding (Substitution)
import Agda.TypeChecking.Rules.LHS.ProblemRest
import Agda.TypeChecking.Rules.LHS.Unify
import Agda.TypeChecking.Rules.LHS.Split
import Agda.TypeChecking.Rules.LHS.Implicit
import Agda.TypeChecking.Rules.LHS.Instantiate
import Agda.TypeChecking.Rules.Data

import Agda.Utils.Except (MonadError(..))
import Agda.Utils.Functor
import Agda.Utils.List
import Agda.Utils.ListT
import Agda.Utils.Maybe
import Agda.Utils.Monad
import Agda.Utils.Permutation
import Agda.Utils.Size

#include "undefined.h"
import Agda.Utils.Impossible

-- | Compute the set of flexible patterns in a list of patterns. The result is
--   the deBruijn indices of the flexible patterns.
flexiblePatterns :: [NamedArg A.Pattern] -> TCM FlexibleVars
flexiblePatterns nps = do
  forMaybeM (zip (downFrom $ length nps) nps) $ \ (i, Arg ai p) -> do
    runMaybeT $ (\ f -> FlexibleVar (getHiding ai) f (Just i) i) <$> maybeFlexiblePattern p

-- | A pattern is flexible if it is dotted or implicit, or a record pattern
--   with only flexible subpatterns.
class IsFlexiblePattern a where
  maybeFlexiblePattern :: a -> MaybeT TCM FlexibleVarKind

  isFlexiblePattern :: a -> TCM Bool
  isFlexiblePattern p = isJust <$> runMaybeT (maybeFlexiblePattern p)

instance IsFlexiblePattern A.Pattern where
  maybeFlexiblePattern p =
    case p of
      A.DotP{}  -> return DotFlex
      A.VarP{}  -> return ImplicitFlex
      A.WildP{} -> return ImplicitFlex
      A.AsP _ _ p -> maybeFlexiblePattern p
      A.ConP _ (A.AmbQ [c]) qs
        -> ifM (isNothing <$> isRecordConstructor c) mzero {-else-}
             (maybeFlexiblePattern qs)
      _ -> mzero

instance IsFlexiblePattern (I.Pattern' a) where
  maybeFlexiblePattern p =
    case p of
      I.DotP{}  -> return DotFlex
      I.ConP _ i ps
        | Just ConOSystem <- conPRecord i -> return ImplicitFlex  -- expanded from ImplicitP
        | Just _            <- conPRecord i -> maybeFlexiblePattern ps
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

-- | Update the in patterns according to the given substitution, collecting
--   new dot pattern instantiations in the process.
updateInPatterns
 :: [Dom Type]              -- ^ the types of the old pattern variables,
                              --   relative to the new telescope
 -> [NamedArg A.Pattern]    -- ^ old in patterns
 -> [Arg DeBruijnPattern] -- ^ patterns to be substituted, living in the
                              --   new telescope
 -> TCM ([NamedArg A.Pattern]   -- new in patterns
        ,[DotPatternInst])        -- new dot pattern instantiations
updateInPatterns as ps qs = do
  reportSDoc "tc.lhs.top" 20 $ text "updateInPatterns" <+> nest 2 (vcat
    [ text "as      =" <+> prettyList (map prettyTCM as)
    , text "ps      =" <+> prettyList (map prettyA ps)
    , text "qs      =" <+> prettyList (map (text . show) qs)
    ])
  first (map snd . IntMap.toDescList) <$> updates as ps qs
  where
    updates :: [Dom Type] -> [NamedArg A.Pattern] -> [Arg DeBruijnPattern]
           -> TCM (IntMap (NamedArg A.Pattern), [DotPatternInst])
    updates as ps qs = mconcat <$> sequence (zipWith3 update as ps qs)

    update :: Dom Type -> NamedArg A.Pattern -> Arg DeBruijnPattern
           -> TCM (IntMap (NamedArg A.Pattern), [DotPatternInst])
    update a p q = case unArg q of
      -- Case: the unifier did not instantiate the variable
      VarP x     -> return (IntMap.singleton (dbPatVarIndex x) p, [])
      -- Case: the unifier did instantiate the variable
      DotP u     -> case snd $ asView $ namedThing (unArg p) of
        A.DotP _ _ e -> return (IntMap.empty, [DPI Nothing  (Just e) u a])
        A.WildP _  -> return (IntMap.empty, [DPI Nothing  Nothing  u a])
        A.VarP x   -> return (IntMap.empty, [DPI (Just x) Nothing  u a])
        A.ConP _ (A.AmbQ [c]) qs -> do
          Def r es  <- ignoreSharing <$> reduce (unEl $ unDom a)
          let vs = fromMaybe __IMPOSSIBLE__ $ allApplyElims es
          (ftel, us) <- etaExpandRecord r vs u
          qs <- insertImplicitPatterns ExpandLast qs ftel
          let instTel EmptyTel _                   = []
              instTel (ExtendTel arg tel) (u : us) = arg : instTel (absApp tel u) us
              instTel ExtendTel{} []               = __IMPOSSIBLE__
              bs0 = instTel ftel (map unArg us)
              -- Andreas, 2012-09-19 propagate relevance info to dot patterns
              bs  = map (mapRelevance (composeRelevance (getRelevance a))) bs0
          updates bs qs (map (DotP . unArg) us `withArgsFrom` teleArgNames ftel)
        A.AsP         _ _ _ -> __IMPOSSIBLE__
        A.ConP        _ _ _ -> __IMPOSSIBLE__
        A.RecP        _ _   -> __IMPOSSIBLE__
        A.ProjP       _ _ _ -> __IMPOSSIBLE__
        A.DefP        _ _ _ -> __IMPOSSIBLE__
        A.AbsurdP     _     -> __IMPOSSIBLE__
        A.LitP        _     -> __IMPOSSIBLE__
        A.PatternSynP _ _ _ -> __IMPOSSIBLE__
      -- Case: the unifier eta-expanded the variable
      ConP c cpi qs -> do
        Def r es <- ignoreSharing <$> reduce (unEl $ unDom a)
        def      <- theDef <$> getConstInfo r
        let pars = fromMaybe __IMPOSSIBLE__ $ allApplyElims es
            fs  = killRange $ recFields def
            tel = recTel def `apply` pars
            as  = applyPatSubst (parallelS $ map (namedThing . unArg) qs) $ flattenTel tel
            -- If the user wrote a dot pattern or variable but the unifier
            -- eta-expanded it, add the corresponding instantiation.
            dpi :: [DotPatternInst]
            dpi = mkDPI $ patternToTerm $ unArg q
              where
                mkDPI v = case namedThing $ unArg p of
                  A.DotP _ _ e -> [DPI Nothing (Just e) v a]
                  A.VarP x     -> [DPI (Just x) Nothing v a]
                  _            -> []
        second (dpi++) <$>
          updates as (projectInPat p fs) (map (fmap namedThing) qs)
      LitP _     -> __IMPOSSIBLE__
      ProjP{}    -> __IMPOSSIBLE__

    projectInPat :: NamedArg A.Pattern -> [Arg QName] -> [NamedArg A.Pattern]
    projectInPat p fs = case namedThing (unArg p) of
      A.VarP x            -> map (makeWildField (PatRange $ getRange x)) fs
      A.ConP cpi _ nps    -> nps
      A.WildP pi          -> map (makeWildField pi) fs
      A.DotP pi o e       -> map (makeDotField pi o) fs
      A.ProjP _ _ _       -> __IMPOSSIBLE__
      A.DefP _ _ _        -> __IMPOSSIBLE__
      A.AsP _ _ _         -> __IMPOSSIBLE__
      A.AbsurdP _         -> __IMPOSSIBLE__
      A.LitP _            -> __IMPOSSIBLE__
      A.PatternSynP _ _ _ -> __IMPOSSIBLE__
      A.RecP _ _          -> __IMPOSSIBLE__
      where
        makeWildField pi (Arg fi f) = Arg fi $ unnamed $ A.WildP pi
        makeDotField pi o (Arg fi f) = Arg fi $ unnamed $
          A.DotP pi o $ A.Underscore underscoreInfo
          where
            underscoreInfo = A.MetaInfo
              { A.metaRange          = getRange pi
              , A.metaScope          = emptyScopeInfo
              , A.metaNumber         = Nothing
              , A.metaNameSuggestion = show $ A.nameConcrete $ qnameName f
              }


-- | Check if a problem is solved. That is, if the patterns are all variables.
isSolvedProblem :: Problem -> Bool
isSolvedProblem problem = null (restPats $ problemRest problem) &&
    all (isSolved . snd . asView . namedArg) (problemInPat problem)
  where
    -- need further splitting:
    isSolved A.ConP{}        = False
    isSolved A.LitP{}        = False
    isSolved A.ProjP{}       = False
    isSolved A.RecP{}        = False  -- record pattern
    -- solved:
    isSolved A.VarP{}        = True
    isSolved A.WildP{}       = True
    isSolved A.DotP{}        = True
    isSolved A.AbsurdP{}     = True
    -- impossible:
    isSolved A.DefP{}        = __IMPOSSIBLE__
    isSolved A.AsP{}         = __IMPOSSIBLE__  -- removed by asView
    isSolved A.PatternSynP{} = __IMPOSSIBLE__  -- expanded before

-- | For each user-defined pattern variable in the 'Problem', check
-- that the corresponding data type (if any) does not contain a
-- constructor of the same name (which is not in scope); this
-- \"shadowing\" could indicate an error, and is not allowed.
--
-- Precondition: The problem has to be solved.

noShadowingOfConstructors
  :: Call -- ^ Trace, e.g., @CheckPatternShadowing clause@
  -> Problem -> TCM ()
noShadowingOfConstructors mkCall problem =
  traceCall mkCall $ do
    let pat = map (snd . asView . namedArg) $
                  problemInPat problem
        tel = map (unEl . snd . unDom) $ telToList $ problemTel problem
    zipWithM_ noShadowing pat tel -- TODO: does not work for flexible arity and projection patterns
    return ()
  where
  noShadowing (A.WildP     {}) t = return ()
  noShadowing (A.AbsurdP   {}) t = return ()
  noShadowing (A.ConP      {}) t = return ()  -- only happens for eta expanded record patterns
  noShadowing (A.RecP      {}) t = return ()  -- record pattern
  noShadowing (A.ProjP     {}) t = return ()  -- projection pattern
  noShadowing (A.DefP      {}) t = __IMPOSSIBLE__
  noShadowing (A.DotP      {}) t = return ()
  noShadowing (A.AsP       {}) t = __IMPOSSIBLE__
  noShadowing (A.LitP      {}) t = __IMPOSSIBLE__
  noShadowing (A.PatternSynP {}) t = __IMPOSSIBLE__
  noShadowing (A.VarP x)       t = do
    reportSDoc "tc.lhs.shadow" 30 $ vcat
      [ text $ "checking whether pattern variable " ++ show x ++ " shadows a constructor"
      , nest 2 $ text "type of variable =" <+> prettyTCM t
      ]
    reportSLn "tc.lhs.shadow" 70 $ "  t = " ++ show t
    t <- reduce t
    case t of
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
      Shared p -> noShadowing (A.VarP x) $ derefPtr p
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
      DontCare{} -> __IMPOSSIBLE__

-- | Check that a dot pattern matches it's instantiation.
checkDotPattern :: DotPatternInst -> TCM ()
checkDotPattern (DPI _ (Just e) v (Dom info a)) =
  traceCall (CheckDotPattern e v) $ do
  reportSDoc "tc.lhs.dot" 15 $
    sep [ text "checking dot pattern"
        , nest 2 $ prettyA e
        , nest 2 $ text "=" <+> prettyTCM v
        , nest 2 $ text ":" <+> prettyTCM a
        ]
  applyRelevanceToContext (argInfoRelevance info) $ do
    u <- checkExpr e a
    reportSDoc "tc.lhs.dot" 30 $
      sep [ text "equalTerm"
          , nest 2 $ text $ show a
          , nest 2 $ text $ show u
          , nest 2 $ text $ show v
          ]
    -- Should be ok to do noConstraints here
    noConstraints $ equalTerm a u v
checkDotPattern (DPI _ Nothing _ _) = return ()

-- | Temporary data structure for 'checkLeftoverPatterns'
type Projectn  = (ProjOrigin, QName)
type Projectns = [Projectn]

-- | Checks whether the dot patterns left over after splitting can be covered
--   by shuffling around the dots from implicit positions. Returns the updated
--   user patterns (without dot patterns).
checkLeftoverDotPatterns
  :: [NamedArg A.Pattern] -- ^ Leftover patterns after splitting is completed
  -> [Int]                -- ^ De Bruijn indices of leftover variable patterns
                          --   computed by splitting
  -> [Dom Type]           -- ^ Types of leftover patterns
  -> [DotPatternInst]     -- ^ Instantiations computed by unifier
  -> TCM ()
checkLeftoverDotPatterns ps vs as dpi = do
  reportSDoc "tc.lhs.dot" 15 $ text "checking leftover dot patterns..."
  idv <- sortBy (compare `on` length . snd) . concat <$>
           traverse gatherImplicitDotVars dpi
  reportSDoc "tc.lhs.dot" 30 $ nest 2 $
    text "implicit dotted variables:" <+>
    prettyList (map (\(i,fs) -> prettyTCM $ Var i (map (uncurry Proj) fs)) idv)
  checkUserDots ps vs as idv
  reportSDoc "tc.lhs.dot" 15 $ text "all leftover dot patterns ok!"

  where
    checkUserDots :: [NamedArg A.Pattern] -> [Int] -> [Dom Type]
                  -> [(Int,Projectns)]
                  -> TCM ()
    checkUserDots []     []     []     idv = return ()
    checkUserDots []     (_:_)  _      idv = __IMPOSSIBLE__
    checkUserDots []     _      (_:_)  idv = __IMPOSSIBLE__
    checkUserDots (_:_)  []     _      idv = __IMPOSSIBLE__
    checkUserDots (_:_)  _      []     idv = __IMPOSSIBLE__
    checkUserDots (p:ps) (v:vs) (a:as) idv = do
      idv' <- checkUserDot p v a idv
      checkUserDots ps vs as idv'

    checkUserDot :: NamedArg A.Pattern -> Int -> Dom Type
                 -> [(Int,Projectns)]
                 -> TCM [(Int,Projectns)]
    checkUserDot p v a idv = case namedArg p of
      A.DotP i o e | o == Inserted -> return idv
      -- Jesper, 2016-12-08 (Issue 1605): if the origin is Inserted, this
      -- means the dot pattern was created by expanding '...', so we don't
      -- have to complain here.
      A.DotP i o e -> do
        reportSDoc "tc.lhs.dot" 30 $ nest 2 $
          text "checking user dot pattern: " <+> prettyA e
        caseMaybeM (undotImplicitVar (v,[],unDom a) idv)
          (traceCall (CheckPattern (namedArg p) EmptyTel (unDom a)) $
             typeError $ UninstantiatedDotPattern e)
          (\idv' -> do
            u <- checkExpr e (unDom a)
            reportSDoc "tc.lhs.dot" 30 $ nest 2 $
              text "checked expression: " <+> prettyTCM u
            noConstraints $ equalTerm (unDom a) u (var v)
            return idv')
      A.VarP _     -> return idv
      A.WildP _    -> return idv
      A.AbsurdP _  -> return idv
      A.ConP _ _ _ -> __IMPOSSIBLE__
      A.LitP _     -> __IMPOSSIBLE__
      A.ProjP _ _ _-> __IMPOSSIBLE__
      A.DefP _ _ _ -> __IMPOSSIBLE__
      A.RecP _ _   -> __IMPOSSIBLE__
      A.AsP  _ _ _ -> __IMPOSSIBLE__
      A.PatternSynP _ _ _ -> __IMPOSSIBLE__

    gatherImplicitDotVars :: DotPatternInst -> TCM [(Int,Projectns)]
    gatherImplicitDotVars (DPI _ (Just _) _ _) = return [] -- Not implicit
    gatherImplicitDotVars (DPI _ Nothing u _)  = gatherVars u
      where
        gatherVars :: Term -> TCM [(Int,Projectns)]
        gatherVars u = case ignoreSharing u of
          Var i es -> return $ (i,) <$> maybeToList (allProjElims es)
          Con c _ us -> ifM (isEtaCon $ conName c)
                      {-then-} (concat <$> traverse (gatherVars . unArg) us)
                      {-else-} (return [])
          _        -> return []

    lookupImplicitDotVar :: (Int,Projectns) -> [(Int,Projectns)] -> Maybe Projectns
    lookupImplicitDotVar (i,fs) [] = Nothing
    lookupImplicitDotVar (i,fs) ((j,gs):js)
     -- Andreas, 2016-09-20, issue #2196
     -- We need to ignore the ProjOrigin!
     | i == j , Just hs <- stripPrefixBy ((==) `on` snd) fs gs = Just hs
     | otherwise = lookupImplicitDotVar (i,fs) js

    undotImplicitVar :: (Int,Projectns,Type) -> [(Int,Projectns)]
                     -> TCM (Maybe [(Int,Projectns)])
    undotImplicitVar (i,fs,a) idv = do
     reportSDoc "tc.lhs.dot" 40 $ vcat
       [ text "undotImplicitVar"
       , nest 2 $ vcat
         [ text $ "i  =  " ++ show i
         , text   "fs = " <+> sep (map (prettyTCM . snd) fs)
         , text   "a  = " <+> prettyTCM a
         , text $ "raw=  "  ++ show a
         , text $ "idv=  "  ++ show idv
         ]
       ]
     case lookupImplicitDotVar (i,fs) idv of
      Nothing -> return Nothing
      Just [] -> return $ Just $ delete (i,fs) idv
      Just rs -> caseMaybeM (isEtaRecordType a) (return Nothing) $ \(d,pars) -> do
        gs <- recFields . theDef <$> getConstInfo d
        let u = Var i (map (uncurry Proj) fs)
        is <- forM gs $ \(Arg _ g) -> do
                (_,_,b) <- fromMaybe __IMPOSSIBLE__ <$> projectTyped u a ProjSystem g
                return (i,fs++[(ProjSystem,g)],b)
        undotImplicitVars is idv

    undotImplicitVars :: [(Int,Projectns,Type)] -> [(Int,Projectns)]
                      -> TCM (Maybe [(Int,Projectns)])
    undotImplicitVars []     idv = return $ Just idv
    undotImplicitVars (i:is) idv =
      caseMaybeM (undotImplicitVar i idv)
        (return Nothing)
        (\idv' -> undotImplicitVars is idv')


-- | Bind the variables in a left hand side and check that 'Hiding' of
--   the patterns matches the hiding info in the type.
--
--   Precondition: the patterns should
--   all be 'A.VarP', 'A.WildP', or 'A.AbsurdP' and the
--   telescope should have the same size as the pattern list.
--   There could also be 'A.ConP's resulting from eta expanded implicit record
--   patterns.
bindLHSVars :: [NamedArg A.Pattern] -> Telescope -> TCM a -> TCM a
bindLHSVars []        tel@ExtendTel{}  _   = do
  reportSDoc "impossible" 10 $
    text "bindLHSVars: no patterns left, but tel =" <+> prettyTCM tel
  __IMPOSSIBLE__
bindLHSVars (_ : _)   EmptyTel         _   = __IMPOSSIBLE__
bindLHSVars []        EmptyTel         ret = ret
bindLHSVars (p : ps) (ExtendTel a tel) ret = do
  -- see test/Fail/WronHidingInLHS:
  unless (getHiding p == getHiding a) $ typeError WrongHidingInLHS

  case namedArg p of
    A.VarP x      -> addContext (x, a) $ bindLHSVars ps (absBody tel) ret
    A.WildP _     -> bindDummy (absName tel)
                 -- @bindDummy underscore@ does not fix issue 819, but
                 -- introduces unwanted underscores in error messages
                 -- (Andreas, 2015-05-28)
    A.DotP _ _ _  -> bindDummy (absName tel)
    A.AbsurdP pi  -> do
      -- Andreas, 2012-03-15: allow postponement of emptyness check
      isEmptyType (getRange pi) $ unDom a
      -- OLD CODE: isReallyEmptyType $ unArg a
      bindDummy (absName tel)
    A.ConP{}        -> __IMPOSSIBLE__
    A.RecP{}        -> __IMPOSSIBLE__
    A.ProjP{}       -> __IMPOSSIBLE__
    A.DefP{}        -> __IMPOSSIBLE__
    A.AsP{}         -> __IMPOSSIBLE__
    A.LitP{}        -> __IMPOSSIBLE__
    A.PatternSynP{} -> __IMPOSSIBLE__
    where
      bindDummy s = do
        x <- if isUnderscore s then freshNoName_ else unshadowName =<< freshName_ ("." ++ argNameToString s)
        addContext (x, a) $ bindLHSVars ps (absBody tel) ret

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
  instantiateFull' (LHSResult n tel ps t sub as) = LHSResult n
    <$> instantiateFull' tel
    <*> instantiateFull' ps
    <*> instantiateFull' t
    <*> instantiateFull' sub
    <*> instantiateFull' as

-- | Check a LHS. Main function.
--
--   @checkLeftHandSide a ps a ret@ checks that user patterns @ps@ eliminate
--   the type @a@ of the defined function, and calls continuation @ret@
--   if successful.

checkLeftHandSide
  :: Call
     -- ^ Trace, e.g. @CheckPatternShadowing clause@
  -> Maybe QName
     -- ^ The name of the definition we are checking.
  -> [NamedArg A.Pattern]
     -- ^ The patterns.
  -> Type
     -- ^ The expected type @a = Γ → b@.
  -> Maybe Substitution
     -- ^ Module parameter substitution from with-abstraction.
  -> (LHSResult -> TCM a)
     -- ^ Continuation.
  -> TCM a
checkLeftHandSide c f ps a withSub' = Bench.billToCPS [Bench.Typing, Bench.CheckLHS] $ \ ret -> do

  -- To allow module parameters to be refined by matching, we're adding the
  -- context arguments as wildcard patterns and extending the type with the
  -- context telescope.
  cxt <- reverse <$> getContext
  let tel = telFromList' show cxt
      cps = [ unnamed . A.VarP . fst <$> setOrigin Inserted (argFromDom d)
            | d <- cxt ]
  problem0 <- problemFromPats (cps ++ ps) (telePi tel a)
  -- Andreas, 2013-03-15 deactivating the following test allows
  -- flexible arity
  -- unless (noProblemRest problem) $ typeError $ TooManyArgumentsInLHS a

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

  -- doing the splits:
  inTopContext $ do
    LHSState problem@(Problem pxs qs delta rest) dpi
      <- checkLHS f $ LHSState problem0 []

    unless (null $ restPats rest) $ typeError $ TooManyArgumentsInLHS a

    addContext delta $ do
      noShadowingOfConstructors c problem
      noPatternMatchingOnCodata qs

    -- f is Nothing when checking let pattern-bindings. In that case there can
    -- be no copatterns, so we don't need to worry about self.
    let self = Def (fromMaybe __IMPOSSIBLE__ f) []
    asb <- addContext delta $ recoverAsPatterns delta (telePi tel a) self (cps ++ ps) qs

    reportSDoc "tc.lhs.top" 10 $
      vcat [ text "checked lhs:"
           , nest 2 $ vcat
             [ text "pxs   = " <+> fsep (map prettyA pxs)
             , text "delta = " <+> prettyTCM delta
             , text "dpi   = " <+> addContext delta (brackets $ fsep $ punctuate comma $ map prettyTCM dpi)
             , text "asb   = " <+> addContext delta (brackets $ fsep $ punctuate comma $ map prettyTCM asb)
             , text "qs    = " <+> prettyList (map pretty qs)
             ]
           ]

    let b' = restType rest
    bindLHSVars (filter (isNothing . isProjP) pxs) delta $ do
      let -- Find the variable patterns that have been refined
          refinedParams = [ AsB x v (unDom a) | DPI (Just x) _ v a <- dpi ]
          asb'          = refinedParams ++ asb

      reportSDoc "tc.lhs.top" 10 $ text "asb' = " <+> (brackets $ fsep $ punctuate comma $ map prettyTCM asb')

      reportSDoc "tc.lhs.top" 10 $ text "bound pattern variables"
      reportSDoc "tc.lhs.top" 60 $ nest 2 $ text "context = " <+> ((text . show) =<< getContext)
      reportSDoc "tc.lhs.top" 10 $ nest 2 $ text "type  = " <+> prettyTCM b'
      reportSDoc "tc.lhs.top" 60 $ nest 2 $ text "type  = " <+> text (show b')

      let notProj ProjP{} = False
          notProj _       = True
                      -- Note: This works because we can't change the number of
                      --       arguments in the lhs of a with-function relative to
                      --       the parent function.
          numPats   = length $ takeWhile (notProj . namedArg) qs
          -- In the case of a non-with function the pattern substitution
          -- should be weakened by the number of non-parameter patterns to
          -- get the paramSub.
          withSub = fromMaybe (wkS (numPats - length cxt) idS) withSub'
          -- At this point we need to update the module parameters for all
          -- parent modules.
          patSub   = (map (patternToTerm . namedArg) $ reverse $ take numPats qs) ++# EmptyS
          paramSub = composeS patSub withSub
          lhsResult = LHSResult (length cxt) delta qs b' patSub asb'
      reportSDoc "tc.lhs.top" 20 $ nest 2 $ text "patSub   = " <+> text (show patSub)
      reportSDoc "tc.lhs.top" 20 $ nest 2 $ text "withSub  = " <+> text (show withSub)
      reportSDoc "tc.lhs.top" 20 $ nest 2 $ text "paramSub = " <+> text (show paramSub)

      let newLets = [ AsB x (applySubst paramSub v) (applySubst paramSub $ unDom a) | (x, (v, a)) <- oldLets ]
      reportSDoc "tc.lhs.top" 50 $ text "old let-bindings:" <+> text (show oldLets)
      reportSDoc "tc.lhs.top" 50 $ text "new let-bindings:" <+> (brackets $ fsep $ punctuate comma $ map prettyTCM newLets)

      bindAsPatterns newLets $
        applyRelevanceToContext (getRelevance b') $ updateModuleParameters paramSub $ do
        bindAsPatterns asb' $ do

          rebindLocalRewriteRules

          -- Check dot patterns
          mapM_ checkDotPattern dpi
          checkLeftoverDotPatterns pxs (downFrom $ size delta) (flattenTel delta) dpi

        -- Issue2303: don't bind asb' for the continuation (return in lhsResult instead)
        ret lhsResult

-- | The loop (tail-recursive): split at a variable in the problem until problem is solved
checkLHS
  :: Maybe QName       -- ^ The name of the definition we are checking.
  -> LHSState          -- ^ The current state.
  -> TCM LHSState      -- ^ The final state after all splitting is completed
checkLHS f st@(LHSState problem dpi) = do

  problem <- insertImplicitProblem problem
  -- Note: inserting implicits no longer preserve solvedness,
  -- since we might insert eta expanded record patterns.
  if isSolvedProblem problem then return $ st { lhsProblem = problem } else do

    unlessM (optPatternMatching <$> gets getPragmaOptions) $
      typeError $ GenericError $ "Pattern matching is disabled"

    foldListT trySplit nothingToSplit $ splitProblem f problem
  where

    nothingToSplit = do
      reportSLn "tc.lhs.split" 50 $ "checkLHS: nothing to split in problem " ++ show problem
      nothingToSplitError problem

    -- Split problem rest (projection pattern, does not fail as there is no call to unifier)

    trySplit (SplitRest projPat o projType) _ = do

      -- Compute the new problem
      let Problem ps1 ip delta (ProblemRest (p:ps2) b) = problem
          -- ps'      = ps1 ++ [p]
          ps'      = ps1 -- drop the projection pattern (already splitted)
          rest     = ProblemRest ps2 (projPat $> projType)
          ip'      = ip ++ [fmap (Named Nothing . ProjP o) projPat]
          problem' = Problem ps' ip' delta rest
      -- Jump the trampolin
      st' <- updateProblemRest (LHSState problem' dpi)
      -- If the field is irrelevant, we need to continue in irr. cxt.
      -- (see Issue 939).
      applyRelevanceToContext (getRelevance projPat) $ do
        checkLHS f st'

    -- Split on literal pattern (does not fail as there is no call to unifier)

    trySplit (Split p0 (Arg _ (LitFocus lit ip a)) p1) _ = do

      -- substitute the literal in p1 and dpi
      let delta1 = problemTel p0
          delta2 = absApp (fmap problemTel p1) (Lit lit)
          rho    = singletonS (size delta2) (LitP lit)
          -- Andreas, 2015-06-13 Literals are closed, so need to raise them!
          -- rho    = liftS (size delta2) $ singletonS 0 (Lit lit)
          -- rho    = [ var i | i <- [0..size delta2 - 1] ]
          --       ++ [ raise (size delta2) $ Lit lit ]
          --       ++ [ var i | i <- [size delta2 ..] ]
          dpi'     = applyPatSubst rho dpi
          ip'      = applySubst rho ip
          rest'    = applyPatSubst rho (problemRest problem)

      -- Compute the new problem
      let ps'      = problemInPat p0 ++ problemInPat (absBody p1)
          delta'   = abstract delta1 delta2
          problem' = Problem ps' ip' delta' rest'
      st' <- updateProblemRest (LHSState problem' dpi')
      checkLHS f st'

    -- Split on constructor pattern (unifier might fail)

    trySplit (Split p0 focus@(Arg info Focus{}) p1) tryNextSplit = do
      res <- trySplitConstructor p0 focus p1
      case res of
        -- Success.  Continue checking LHS.
        Unifies st'    -> checkLHS f st'
        -- Mismatch.  Report and abort.
        NoUnify  tcerr -> throwError tcerr
        -- Unclear situation.  Try next split.
        -- If no split works, give error from first split.
        -- This is conservative, but might not be the best behavior.
        -- It might be better to collect all the errors and print all of them.
        DontKnow tcerr -> tryNextSplit `catchError` \ _ -> throwError tcerr

    whenUnifies
      :: UnificationResult' a
      -> (a -> TCM (UnificationResult' b))
      -> TCM (UnificationResult' b)
    whenUnifies res cont = do
      case res of
        Unifies a      -> cont a
        NoUnify  tcerr -> return $ NoUnify  tcerr
        DontKnow tcerr -> return $ DontKnow tcerr

    trySplitConstructor p0 (Arg info LitFocus{}) p1 = __IMPOSSIBLE__
    trySplitConstructor p0 (Arg info
             (Focus { focusCon      = c
                    , focusPatOrigin= porigin
                    , focusConArgs  = qs
                    , focusRange    = r
                    , focusOutPat   = ip
                    , focusDatatype = d
                    , focusParams   = vs
                    , focusIndices  = ws
                    , focusType     = a
                    }
             )) p1 = do
      traceCall (CheckPattern (A.ConP (ConPatInfo porigin $ PatRange r) (A.AmbQ [c]) qs)
                                       (problemTel p0)
                                       (El Prop $ Def d $ map Apply $ vs ++ ws)) $ do

        let delta1 = problemTel p0
            delta2 = problemTel $ absBody p1
        let typeOfSplitVar = Arg info a

        reportSDoc "tc.lhs.split" 10 $ sep
          [ text "checking lhs"
          , nest 2 $ text "tel =" <+> prettyTCM (problemTel problem)
          , nest 2 $ text "rel =" <+> (text $ show $ argInfoRelevance info)
          ]

        reportSDoc "tc.lhs.split" 15 $ sep
          [ text "split problem"
          , nest 2 $ vcat
            [ text "delta1 = " <+> prettyTCM delta1
            , text "typeOfSplitVar =" <+> addContext delta1 (prettyTCM typeOfSplitVar)
            , text "focusOutPat =" <+> (text . show) ip
            , text "delta2 = " <+> addContext delta1 (addContext ("x",domFromArg typeOfSplitVar) (prettyTCM delta2))
            ]
          ]

        c <- (`withRangeOf` c) <$> getConForm c
        ca <- defType <$> getConInfo c

        reportSDoc "tc.lhs.split" 20 $ nest 2 $ vcat
          [ text "ca =" <+> prettyTCM ca
          , text "vs =" <+> prettyList (map prettyTCM vs)
          ]

        -- Lookup the type of the constructor at the given parameters
        let a = ca `piApply` vs

        -- It will end in an application of the datatype
        (gamma', ca, d', us) <- do
          TelV gamma' ca@(El _ def) <- telView a
          let Def d' es = ignoreSharing def
              Just us   = allApplyElims es
          return (gamma', ca, d', us)

        -- This should be the same datatype as we split on
        unless (d == d') $ typeError $ ShouldBeApplicationOf ca d'

        reportSDoc "tc.lhs.top" 20 $ addContext delta1 $ nest 2 $ vcat
          [ text "gamma' =" <+> prettyTCM gamma'
          ]

        -- Andreas 2010-09-07  propagate relevance info to new vars
        let updRel = composeRelevance (getRelevance info)
        gamma' <- return $ mapRelevance updRel <$> gamma'

        -- Insert implicit patterns
        qs' <- insertImplicitPatterns ExpandLast qs gamma'

        unless ((size qs' :: Int) == size gamma') $
          typeError $ WrongNumberOfConstructorArguments (conName c) (size gamma') (size qs')

        let gamma = useNamesFromPattern qs' gamma'

        -- Get the type of the datatype.
        da <- (`piApply` vs) . defType <$> getConstInfo d

        -- Compute the flexible variables
        flex <- flexiblePatterns (problemInPat p0 ++ qs')

        -- Compute the constructor indices by dropping the parameters
        let us' = drop (size vs) us

        reportSDoc "tc.lhs.top" 15 $ addContext delta1 $
          sep [ text "preparing to unify"
              , nest 2 $ vcat
                [ text "c      =" <+> prettyTCM c <+> text ":" <+> prettyTCM a
                , text "d      =" <+> prettyTCM (Def d (map Apply $ vs++ws)) <+> text ":" <+> prettyTCM da
                , text "gamma  =" <+> prettyTCM gamma
                , text "gamma' =" <+> prettyTCM gamma'
                , text "vs     =" <+> brackets (fsep $ punctuate comma $ map prettyTCM vs)
                , text "us'    =" <+> addContext gamma (brackets (fsep $ punctuate comma $ map prettyTCM us'))
                , text "ws     =" <+> brackets (fsep $ punctuate comma $ map prettyTCM ws)
                ]
              ]

        -- Unify constructor target and given type (in Δ₁Γ)
        -- Given: Δ₁ ⊢ D vs : Φ → Setᵢ
        --        Δ₁ ⊢ c    : Γ → D vs' us'
        --        Δ₁ ⊢ ws   : Φ
        --        Δ₁Γ ⊢ ws' : Φ
        -- (where vs' = raise Γ vs and ws' = raise Γ ws)
        -- unification of us' and ws' in context Δ₁Γ gives us a telescope Δ₁'
        -- and a substitution ρ₀ such that
        --        Δ₁' ⊢ ρ₀ : Δ₁Γ
        --        Δ₁' ⊢ (us')ρ₀ ≡ (ws')ρ₀ : Φρ₀
        -- We can split ρ₀ into two parts ρ₁ and ρ₂, giving
        --        Δ₁' ⊢ ρ₁ : Δ₁
        --        Δ₁' ⊢ ρ₂ : Γρ₁
        -- Application of the constructor c gives
        --        Δ₁' ⊢ c ρ₂ : (D vs' us')(ρ₁;ρ₂)
        -- We have
        --        us'(ρ₁;ρ₂)
        --         ≡ us'ρ₀      (since ρ₀=ρ₁;ρ₂)
        --         ≡ ws'ρ₀      (by unification)
        --         ≡ ws ρ₁      (since ws doesn't actually depend on Γ)
        -- so     Δ₁' ⊢ c ρ₂ : D (vs)ρ₁ (ws)ρ₁
        -- Putting this together with ρ₁ gives ρ₃ = ρ₁;c ρ₂
        --        Δ₁' ⊢ ρ₁;c ρ₂ : Δ₁(x : D vs ws)
        -- and lifting over Δ₂ gives the final substitution ρ = ρ₃;Δ₂
        -- from Δ' = Δ₁';Δ₂ρ₃
        --        Δ' ⊢ ρ : Δ₁(x : D vs ws)Δ₂

        res <- unifyIndices
                 (delta1 `abstract` gamma)
                 flex
                 (raise (size gamma) da)
                 us'
                 (raise (size gamma) ws)
        whenUnifies res $ \ (delta1',rho0,es) -> do

          reportSDoc "tc.lhs.top" 15 $ text "unification successful"
          reportSDoc "tc.lhs.top" 20 $ nest 2 $ vcat
            [ text "delta1' =" <+> prettyTCM delta1'
            , text "rho0    =" <+> addContext delta1' (prettyTCM rho0)
            , text "es      =" <+> addContext delta1' (prettyTCM $ (fmap . fmap . fmap) patternToTerm es)
            ]

          -- Andreas 2014-11-25  clear 'Forced' and 'Unused'
          -- Andreas 2015-01-19  ... only after unification
          delta1' <- return $ mapRelevance ignoreForced <$> delta1'

          -- compute in patterns for delta1'
          let newPats  = applySubst rho0 $ teleArgs $ delta1 `abstract` gamma
              -- oldTypes are the types of the old pattern variables, but relative
              -- to the *new* telescope delta1'. These are needed to compute the
              -- correct types of new dot pattern instantiations.
              oldTypes = applyPatSubst rho0 $ flattenTel $ delta1 `abstract` gamma
          (p0',newDpi) <- addContext delta1' $ updateInPatterns
                            oldTypes
                            (problemInPat p0 ++ qs')
                            newPats

          reportSDoc "tc.lhs.top" 20 $ addContext delta1' $ nest 2 $ vcat
            [ text "p0'     =" <+> text (show p0')
            , text "newDpi  =" <+> brackets (fsep $ punctuate comma $ map prettyTCM newDpi)
            ]

          -- split substitution into part for Δ₁ and part for Γ
          let (rho1,rho2) = splitS (size gamma) rho0

          reportSDoc "tc.lhs.top" 20 $ addContext delta1' $ nest 2 $ vcat
            [ text "rho1    =" <+> prettyTCM rho1
            , text "rho2    =" <+> prettyTCM rho2
            ]

          -- Andreas, 2010-09-09, save the type.
          -- It is relative to Δ₁, but it should be relative to Δ₁'
          let storedPatternType = applyPatSubst rho1 typeOfSplitVar
          -- Also remember if we are a record pattern and from an implicit pattern.
          isRec <- isRecord d
          let cpi = ConPatternInfo (isRec $> porigin) (Just storedPatternType)

          -- compute final context and permutation
          let crho2   = ConP c cpi $ applySubst rho2 $
                          teleNamedArgs gamma `useOriginFrom` qs'
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
            [ text "crho2   =" <+> text (show crho2)
            , text "rho3    =" <+> text (show rho3)
            , text "delta2' =" <+> text (show delta2')
            ]

          reportSDoc "tc.lhs.top" 15 $ nest 2 $ vcat
            [ text "delta'  =" <+> prettyTCM delta'
            , text "rho     =" <+> addContext delta' (prettyTCM rho)
            ]

          -- compute new in patterns
          let ps'  = p0' ++ problemInPat (absBody p1)

          reportSDoc "tc.lhs.top" 15 $ addContext delta' $
            nest 2 $ vcat
              [ text "ps'    =" <+> brackets (fsep $ punctuate comma $ map prettyA ps')
              ]

          -- The final dpis are the new ones plus the old ones substituted by ρ
          let dpi' = applyPatSubst rho dpi ++ raise (size delta2') newDpi

          reportSDoc "tc.lhs.top" 15 $ addContext delta' $
            nest 2 $ vcat
              [ text "dpi'    =" <+> brackets (fsep $ punctuate comma $ map prettyTCM dpi')
              ]

          -- Apply the substitution
          let ip'      = applySubst rho ip
              rest'    = applyPatSubst rho (problemRest problem)

          reportSDoc "tc.lhs.top" 15 $ addContext delta' $
            nest 2 $ vcat
              [ text "ip' =" <+> text (show ip) ]

          -- Construct the new problem
          let problem' = Problem ps' ip' delta' rest'

          -- if rest type reduces,
          -- extend the split problem by previously not considered patterns
          st'@(LHSState problem'@(Problem ps' ip' delta' rest') dpi')
            <- updateProblemRest $ LHSState problem' dpi'

          reportSDoc "tc.lhs.top" 12 $ sep
            [ text "new problem from rest"
            , nest 2 $ vcat
              [ text "ps'     =" <+> fsep (map prettyA ps')
              , text "delta'  =" <+> prettyTCM delta'
              , text "ip'     =" <+> text (show ip')
              ]
            ]
          return $ Unifies st'


-- | Ensures that we are not performing pattern matching on codata.

noPatternMatchingOnCodata :: [NamedArg DeBruijnPattern] -> TCM ()
noPatternMatchingOnCodata = mapM_ (check . namedArg)
  where
  check (VarP {})   = return ()
  check (DotP {})   = return ()
  check (ProjP{})   = return ()
  check (LitP {})   = return ()  -- Literals are assumed not to be coinductive.
  check (ConP con _ ps) = do
    TelV _ t <- telView' . defType <$> do getConstInfo $ conName con
    c <- isCoinductive t
    case c of
      Nothing    -> __IMPOSSIBLE__
      Just False -> mapM_ (check . namedArg) ps
      Just True  -> typeError $
        GenericError "Pattern matching on coinductive types is not allowed"
