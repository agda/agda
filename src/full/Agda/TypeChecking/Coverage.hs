{-# OPTIONS_GHC -fwarn-unused-imports #-}

{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE TupleSections #-}

{-| Coverage checking, case splitting, and splitting for refine tactics.

 -}

module Agda.TypeChecking.Coverage
  ( SplitClause(..), clauseToSplitClause, fixTarget
  , Covering(..), splitClauses
  , coverageCheck
  , splitClauseWithAbsurd
  , splitLast
  , splitResult
  ) where

import Prelude hiding (null)

import Control.Monad
import Control.Monad.Trans ( lift )

#if !MIN_VERSION_base(4,8,0)
import Control.Applicative hiding (empty)
#endif

import Data.List hiding (null)
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Traversable as Trav

import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.Syntax.Internal.Pattern

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Monad.Exception

import Agda.TypeChecking.Rules.LHS.Problem (flexibleVarFromHiding)
import Agda.TypeChecking.Rules.LHS.Unify
import Agda.TypeChecking.Rules.LHS.Instantiate (instantiateTel)
import Agda.TypeChecking.Rules.LHS (instantiatePattern)

import Agda.TypeChecking.Coverage.Match
import Agda.TypeChecking.Coverage.SplitTree

import Agda.TypeChecking.Datatypes (getConForm)
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Records (isRecordType)
import Agda.TypeChecking.Telescope

import Agda.Interaction.Options

import Agda.Utils.Either
import Agda.Utils.Functor
import Agda.Utils.List
import Agda.Utils.Maybe
import Agda.Utils.Monad
import Agda.Utils.Null
import Agda.Utils.Permutation
import Agda.Utils.Size
import Agda.Utils.Tuple

#include "undefined.h"
import Agda.Utils.Impossible

data SplitClause = SClause
  { scTel    :: Telescope
    -- ^ Type of variables in @scPats@.
  , scPerm   :: Permutation
    -- ^ How to get from the variables in the patterns to the telescope.
  , scPats   :: [NamedArg Pattern]
    -- ^ The patterns leading to the currently considered branch of
    --   the split tree.
  , scSubst  :: Substitution
    -- ^ Substitution from 'scTel' to old context.
    --   Only needed directly after split on variable:
    --   * To update 'scTarget'
    --   * To rename other split variables when splitting on
    --     multiple variables.
    --   @scSubst@ is not ``transitive'', i.e., does not record
    --   the substitution from the original context to 'scTel'
    --   over a series of splits.  It is freshly computed
    --   after each split by 'computeNeighborhood'; also
    --   'splitResult', which does not split on a variable,
    --   should reset it to the identity 'idS', lest it be
    --   applied to 'scTarget' again, leading to Issue 1294.
  , scTarget :: Maybe (Arg Type)
    -- ^ The type of the rhs, living in context 'scTel'.
    --   This invariant is broken before calls to 'fixTarget';
    --   there, 'scTarget' lives in the old context.
    --   'fixTarget' moves 'scTarget' to the new context by applying
    --   substitution 'scSubst'.
  }

-- | A @Covering@ is the result of splitting a 'SplitClause'.
data Covering = Covering
  { covSplitArg     :: Nat  -- ^ De Bruijn level of argument we split on.
  , covSplitClauses :: [(QName, SplitClause)]
      -- ^ Covering clauses, indexed by constructor these clauses share.
  }

-- | Project the split clauses out of a covering.
splitClauses :: Covering -> [SplitClause]
splitClauses (Covering _ qcs) = map snd qcs

-- | Create a split clause from a clause in internal syntax.
clauseToSplitClause :: Clause -> SplitClause
clauseToSplitClause cl = SClause
  { scTel    = clauseTel  cl
  , scPerm   = clausePerm cl
  , scPats   = namedClausePats cl
  , scSubst  = idS  -- Andreas, 2014-07-15  TODO: Is this ok?
  , scTarget = clauseType cl
  }

type CoverM = ExceptionT SplitError TCM

-- | Top-level function for checking pattern coverage.
coverageCheck :: QName -> Type -> [Clause] -> TCM SplitTree
coverageCheck f t cs = do
  TelV gamma a <- telView t
  let -- n             = arity
      -- lgamma/gamma' = telescope of non-dropped arguments
      -- xs            = variable patterns fitting lgamma
      n            = size gamma
      lgamma       = telToList gamma
      xs           = map (argFromDom . fmap (namedVarP . fst)) $ lgamma
      -- construct the initial split clause
      sc           = SClause gamma (idP n) xs idS $ Just $ defaultArg a
  reportSDoc "tc.cover.top" 10 $ vcat
    [ text $ "Coverage checking " ++ show f
    , nest 2 $ vcat $ map (text . show . clausePats) cs
    ]
  -- used = actually used clauses for cover
  -- pss  = uncovered cases
  (splitTree, used, pss) <- cover f cs sc
  reportSDoc "tc.cover.splittree" 10 $ vcat
    [ text "generated split tree for" <+> prettyTCM f
    , text $ show splitTree
    ]
  whenM (optCompletenessCheck <$> pragmaOptions) $
    -- report an error if there are uncovered cases
    unless (null pss) $
        setCurrentRange cs $
          typeError $ CoverageFailure f (map (map $ fmap namedThing) pss)
  -- is = indices of unreachable clauses
  let is = Set.toList $ Set.difference (Set.fromList [0..genericLength cs - 1]) used
  -- report an error if there are unreachable clauses
  unless (null is) $ do
      let unreached = map (cs !!) is
      setCurrentRange unreached $
        typeError $ UnreachableClauses f (map clausePats unreached)
  return splitTree


-- | @cover f cs (SClause _ _ ps _) = return (splitTree, used, pss)@.
--   checks that the list of clauses @cs@ covers the given split clause.
--   Returns the @splitTree@, the @used@ clauses, and missing cases @pss@.
cover :: QName -> [Clause] -> SplitClause ->
         TCM (SplitTree, Set Nat, [[NamedArg Pattern]])
cover f cs sc@(SClause tel perm ps _ target) = do
  reportSDoc "tc.cover.cover" 10 $ vcat
    [ text "checking coverage of pattern:"
    , nest 2 $ text "tel  =" <+> prettyTCM tel
    , nest 2 $ text "perm =" <+> text (show perm)
    , nest 2 $ text "ps   =" <+> text (show ps)
    ]
  let ups = map (fmap namedThing) ps
  exactSplitEnabled <- optExactSplit <$> pragmaOptions
  case match cs ups perm of
    Yes (i,mps)
     | not exactSplitEnabled || (clauseCatchall (cs !! i) || all isTrivialMPattern mps)
     -> do
      reportSLn "tc.cover.cover" 10 $ "pattern covered by clause " ++ show i
      -- Check if any earlier clauses could match with appropriate literals
      let is = [ j | (j, c) <- zip [0..i-1] cs, matchLits c ups perm ]
      reportSLn "tc.cover.cover"  10 $ "literal matches: " ++ show is
      return (SplittingDone (size tel), Set.fromList (i : is), [])

     | otherwise -> do
         reportSDoc "tc.cover.cover" 10 $ vcat
           [ text $ "pattern covered by clause " ++ show i ++ " but case splitting was not exact. remaining mpats: "
           , nest 2 $ vcat $ map (text . show) mps
           ]
         setCurrentRange (cs !! i) $
           typeError $ CoverageNoExactSplit f (cs !! i)

    No        ->  do
      reportSLn "tc.cover" 20 $ "pattern is not covered"
      return (SplittingDone (size tel), Set.empty, [ps])

    -- case: split into projection patterns
    BlockP   -> do
      reportSLn "tc.cover" 20 $ "blocked by projection pattern"
      -- if we want to split projections, but have no target type, we give up
      let done = return (SplittingDone (size tel), Set.empty, [ps])
      caseMaybeM (splitResult f sc) done $ \ (Covering n scs) -> do
        (projs, (trees, useds, psss)) <- mapSnd unzip3 . unzip <$> do
          mapM (traverseF $ cover f cs <=< (snd <.> fixTarget)) scs
          -- OR:
          -- forM scs $ \ (proj, sc') -> (proj,) <$> do
          --   cover f cs =<< do
          --     snd <$> fixTarget sc'
        let tree = SplitAt n $ zip projs trees
        return (tree, Set.unions useds, concat psss)

    -- case: split on variable
    Block bs -> do
      reportSLn "tc.cover.strategy" 20 $ "blocking vars = " ++ show bs
      -- xs is a non-empty lists of blocking variables
      -- try splitting on one of them
      xs <- splitStrategy bs tel
      r <- altM1 (split Inductive sc) xs
      case r of
        Left err  -> case err of
          CantSplit c tel us vs   -> typeError $ CoverageCantSplitOn c tel us vs
          NotADatatype a          -> enterClosure a $ typeError . CoverageCantSplitType
          IrrelevantDatatype a    -> enterClosure a $ typeError . CoverageCantSplitIrrelevantType
          CoinductiveDatatype a   -> enterClosure a $ typeError . CoverageCantSplitType
{- UNUSED
          NoRecordConstructor a   -> typeError $ CoverageCantSplitType a
 -}
          GenericSplitError s     -> fail $ "failed to split: " ++ s
        -- If we get the empty covering, we have reached an impossible case
        -- and are done.
        Right (Covering n []) ->
          return (SplittingDone (size tel), Set.empty, [])
        Right (Covering n scs) -> do
          (trees, useds, psss) <- unzip3 <$> mapM (cover f cs) (map snd scs)
          let tree = SplitAt n $ zipWith (\ (q,_) t -> (q,t)) scs trees
          return (tree, Set.unions useds, concat psss)

splitStrategy :: BlockingVars -> Telescope -> TCM BlockingVars
splitStrategy bs tel = return $ updateLast clearBlockingVarCons xs
  -- Make sure we do not insists on precomputed coverage when
  -- we make our last try to split.
  -- Otherwise, we will not get a nice error message.
  where
    xs       = bs
{- KEEP!
--  Andreas, 2012-10-13
--  The following split strategy which prefers all-constructor columns
--  fails on test/fail/CoverStrategy
    xs       = ys ++ zs
    (ys, zs) = partition allConstructors bs
    allConstructors :: BlockingVar -> Bool
    allConstructors = isJust . snd
-}

-- | Check that a type is a non-irrelevant datatype or a record with
-- named constructor. Unless the 'Induction' argument is 'CoInductive'
-- the data type must be inductive.
isDatatype :: (MonadTCM tcm, MonadException SplitError tcm) =>
              Induction -> Dom Type ->
              tcm (QName, [Arg Term], [Arg Term], [QName])
isDatatype ind at = do
  let t       = unDom at
      throw f = throwException . f =<< do liftTCM $ buildClosure t
  t' <- liftTCM $ reduce t
  case ignoreSharing $ unEl t' of
    Def d es -> do
      let ~(Just args) = allApplyElims es
      def <- liftTCM $ theDef <$> getConstInfo d
      splitOnIrrelevantDataAllowed <- liftTCM $ optExperimentalIrrelevance <$> pragmaOptions
      case def of
        Datatype{dataPars = np, dataCons = cs, dataInduction = i}
          | i == CoInductive && ind /= CoInductive ->
              throw CoinductiveDatatype
          -- Andreas, 2011-10-03 allow some splitting on irrelevant data (if only one constr. matches)
          | isIrrelevant at && not splitOnIrrelevantDataAllowed ->
              throw IrrelevantDatatype
          | otherwise -> do
              let (ps, is) = genericSplitAt np args
              return (d, ps, is, cs)
        Record{recPars = np, recConHead = con, recInduction = i}
          | i == Just CoInductive && ind /= CoInductive ->
              throw CoinductiveDatatype
          | otherwise ->
              return (d, args, [], [conName con])
        _ -> throw NotADatatype
    _ -> throw NotADatatype

-- | Update the target type, add more patterns to split clause
--   if target becomes a function type.
--   Returns the domains of the function type (if any).
fixTarget :: SplitClause -> TCM (Telescope, SplitClause)
fixTarget sc@SClause{ scTel = sctel, scPerm = perm, scPats = ps, scSubst = sigma, scTarget = target } =
  caseMaybe target (return (empty, sc)) $ \ a -> do
    reportSDoc "tc.cover.target" 20 $ sep
      [ text "split clause telescope: " <+> prettyTCM sctel
      , text "old permutation       : " <+> prettyTCM perm
      , text "old patterns          : " <+> sep (map (prettyTCM . namedArg) ps)
      , text "substitution          : " <+> text (show sigma)
      ]
    reportSDoc "tc.cover.target" 30 $ sep
      [ text "target type before substitution (variables may be wrong): " <+> do
          addContext sctel $ prettyTCM a
      ]
    TelV tel b <- telView $ applySubst sigma $ unArg a
    reportSDoc "tc.cover.target" 10 $ sep
      [ text "target type telescope (after substitution): " <+> do
          addContext sctel $ prettyTCM tel
      , text "target type core      (after substitution): " <+> do
          addContext sctel $ addContext tel $ prettyTCM b
      ]
    let n         = size tel
        lgamma    = telToList tel
        xs        = for lgamma $ \ (Dom ai (x, _)) -> Arg ai $ namedVarP "_"
        -- Compute new split clause
        sctel'    = telFromList $ telToList (raise n sctel) ++ lgamma
        perm'     = liftP n $ scPerm sc
        -- Dot patterns in @ps@ need to be raised!  (Issue 1298)
        ps'       = raise n ps ++ xs
        newTarget = Just $ a $> b
        sc'       = SClause
          { scTel    = sctel'
          , scPerm   = perm'
          , scPats   = ps'
          , scSubst  = liftS n $ sigma
          , scTarget = newTarget
          }
    -- Separate debug printing to find cause of crash (Issue 1374)
    reportSDoc "tc.cover.target" 30 $ sep
      [ text "new split clause telescope   : " <+> prettyTCM sctel'
      ]
    reportSDoc "tc.cover.target" 30 $ sep
      [ text "new split clause permutation : " <+> prettyTCM perm'
      ]
    reportSDoc "tc.cover.target" 30 $ sep
      [ text "new split clause patterns    : " <+> sep (map (prettyTCM . namedArg) ps')
      ]
    reportSDoc "tc.cover.target" 30 $ sep
      [ text "new split clause substitution: " <+> text (show $ scSubst sc')
      ]
    reportSDoc "tc.cover.target" 30 $ sep
      [ text "new split clause target      : " <+> do
          addContext sctel' $ prettyTCM $ fromJust newTarget
      ]
    reportSDoc "tc.cover.target" 20 $ sep
      [ text "new split clause"
      , prettyTCM sc'
      ]
    return $ if n == 0 then (empty, sc { scTarget = newTarget }) else (tel, sc')

-- | @computeNeighbourhood delta1 delta2 perm d pars ixs hix hps con@
--
--   @
--      delta1   Telescope before split point
--      n        Name of pattern variable at split point
--      delta2   Telescope after split point
--      d        Name of datatype to split at
--      pars     Data type parameters
--      ixs      Data type indices
--      hix      Index of split variable
--      hps      Patterns with hole at split point
--      con      Constructor to fit into hole
--   @
--   @dtype == d pars ixs@
computeNeighbourhood
  :: Telescope                  -- ^ Telescope before split point.
  -> PatVarName                 -- ^ Name of pattern variable at split point.
  -> Telescope                  -- ^ Telescope after split point.
  -> Permutation                -- ^
  -> QName                      -- ^ Name of datatype to split at.
  -> Args                       -- ^ Data type parameters.
  -> Args                       -- ^ Data type indices.
  -> Nat                        -- ^ Index of split variable.
  -> OneHolePatterns            -- ^ Patterns with hole at split point.
  -> QName                      -- ^ Constructor to fit into hole.
  -> CoverM (Maybe SplitClause) -- ^ New split clause if successful.
computeNeighbourhood delta1 n delta2 perm d pars ixs hix hps c = do

  -- Get the type of the datatype
  dtype <- liftTCM $ (`piApply` pars) . defType <$> getConstInfo d

  -- Get the real constructor name
  con <- liftTCM $ getConForm c
  con <- return $ con { conName = c }  -- What if we restore the current name?
                                       -- Andreas, 2013-11-29 changes nothing!
{-
  con <- conSrcCon . theDef <$> getConstInfo con
  Con con [] <- liftTCM $ ignoreSharing <$> (constructorForm =<< normalise (Con con []))
-}

  -- Get the type of the constructor
  ctype <- liftTCM $ defType <$> getConInfo con

  -- Lookup the type of the constructor at the given parameters
  (gamma0, cixs) <- do
    TelV gamma0 (El _ d) <- liftTCM $ telView (ctype `piApply` pars)
    let Def _ es = ignoreSharing d
        Just cixs = allApplyElims es
    return (gamma0, cixs)

  -- Andreas, 2012-02-25 preserve name suggestion for recursive arguments
  -- of constructor

  let preserve (x, t@(El _ (Def d' _))) | d == d' = (n, t)
      preserve (x, (El s (Shared p))) = preserve (x, El s $ derefPtr p)
      preserve p = p
      gammal = map (fmap preserve) . telToList $ gamma0
      gamma  = telFromList gammal

  debugInit con ctype d pars ixs cixs delta1 delta2 gamma hps hix

  -- All variables are flexible
  -- let flex = [0..size delta1 + size gamma - 1]
  let gammaDelta1  = gammal ++ telToList delta1
      makeFlex i d = flexibleVarFromHiding (getHiding d) i
      flex = zipWith makeFlex [0..] gammaDelta1

  -- Unify constructor target and given type (in Δ₁Γ)
  let conIxs   = drop (size pars) cixs
      givenIxs = raise (size gamma) ixs

  r <- addCtxTel (delta1 `abstract` gamma) $
       unifyIndices flex (raise (size gamma) dtype) conIxs givenIxs

  case r of
    NoUnify {} -> debugNoUnify $> Nothing

    DontKnow{} -> do
      debugCantSplit
      throwException $ CantSplit (conName con) (delta1 `abstract` gamma) conIxs givenIxs
    Unifies sub -> do
      debugSubst "sub" sub

      -- Substitute the constructor for x in Δ₂: Δ₂' = Δ₂[conv/x]
      let conv    = Con con  $ teleArgs gamma   -- Θ Γ ⊢ conv (for any Θ)
          rho0    = consS conv $ raiseS (size gamma)
          -- Andreas, 2015-06-13 share substitution rho0
          delta2' = applySubst rho0 delta2
          -- delta2' = subst 0 conv $ raiseFrom 1 (size gamma) delta2
      debugTel "delta2'" delta2'

      -- Compute a substitution ρ : Δ₁ΓΔ₂' → Δ₁(x:D)Δ₂'
      let rho = liftS (size delta2') $ rho0
             --    [ Var i [] | i <- [0..size delta2' - 1] ]
             -- ++ [ raise (size delta2') conv ]
             -- ++ [ Var i [] | i <- [size delta2' + size gamma ..] ]

      -- Plug the hole with the constructor and apply ρ
      -- Andreas, 2015-05-01  I guess it is fine to use @noConPatternInfo@
      -- as the result of splitting is never used further down the pipeline.
      -- After splitting, Agda reloads the file.
      let conp = ConP con noConPatternInfo $ map (fmap namedVarP) $ teleArgNames gamma
          ps   = plugHole conp hps
          ps'  = applySubst rho ps      -- Δ₁ΓΔ₂' ⊢ ps'
      debugPlugged ps ps'

      -- Δ₁Γ ⊢ sub, we need something in Δ₁ΓΔ₂'
      -- Also needs to be padded with Nothing's to have the right length.
      let pad n xs x = xs ++ replicate (max 0 $ n - size xs) x
          sub'       = replicate (size delta2') Nothing ++
                       pad (size delta1 + size gamma) (raise (size delta2') sub) Nothing
      debugSubst "sub'" sub'

      -- Θ = Δ₁ΓΔ₂'
      let theta = delta1 `abstract` gamma `abstract` delta2'
      debugTel "theta" theta

      -- Apply the unifying substitution to Θ
      -- We get ρ' : Θ' -> Θ
      --        π  : Θ' -> Θ
      (theta', iperm, rho', _) <- liftTCM $ instantiateTel sub' theta
      debugTel "theta'" theta'
      debugShow "iperm" iperm

      -- Compute final permutation
      let perm' = expandP hix (size gamma) perm -- perm' : Θ -> Δ₁(x : D)Δ₂
          rperm = iperm `composeP` perm'
      debugShow "perm'" perm'
      debugShow "rperm" rperm

      -- Compute the final patterns
      let ps'' = instantiatePattern sub' perm' ps'
          rps  = applySubst rho' ps''

      -- Compute the final substitution
      let rsub  = applySubst rho' rho

      debugFinal theta' rperm rps

      return $ Just $ SClause theta' rperm rps rsub Nothing -- target fixed later

  where
    debugInit con ctype d pars ixs cixs delta1 delta2 gamma hps hix =
      liftTCM $ reportSDoc "tc.cover.split.con" 20 $ vcat
        [ text "computeNeighbourhood"
        , nest 2 $ vcat
          [ text "con    =" <+> prettyTCM con
          , text "ctype  =" <+> prettyTCM ctype
          , text "hps    =" <+> text (show hps)
          , text "d      =" <+> prettyTCM d
          , text "pars   =" <+> prettyList (map prettyTCM pars)
          , text "ixs    =" <+> addCtxTel delta1 (prettyList (map prettyTCM ixs))
          , text "cixs   =" <+> do addCtxTel gamma $ prettyList (map prettyTCM cixs)
          , text "delta1 =" <+> prettyTCM delta1
          , text "delta2 =" <+> prettyTCM delta2
          , text "gamma  =" <+> prettyTCM gamma
          , text "hix    =" <+> text (show hix)
          ]
        ]

    debugNoUnify =
      liftTCM $ reportSLn "tc.cover.split.con" 20 "  Constructor impossible!"

    debugCantSplit =
      liftTCM $ reportSLn "tc.cover.split.con" 20 "  Bad split!"

    debugSubst s sub =
      liftTCM $ reportSDoc "tc.cover.split.con" 20 $ nest 2 $ vcat
        [ text (s ++ " =") <+> brackets (fsep $ punctuate comma $ map (maybe (text "_") prettyTCM) sub)
        ]

    debugTel s tel =
      liftTCM $ reportSDoc "tc.cover.split.con" 20 $ nest 2 $ vcat
        [ text (s ++ " =") <+> prettyTCM tel
        ]

    debugShow s x =
      liftTCM $ reportSDoc "tc.cover.split.con" 20 $ nest 2 $ vcat
        [ text (s ++ " =") <+> text (show x)
        ]

    debugPlugged ps ps' =
      liftTCM $ reportSDoc "tc.cover.split.con" 20 $ nest 2 $ vcat
        [ text "ps     =" <+> text (show ps)
        , text "ps'    =" <+> text (show ps')
        ]

    debugFinal tel perm ps =
      liftTCM $ reportSDoc "tc.cover.split.con" 20 $ nest 2 $ vcat
        [ text "rtel   =" <+> prettyTCM tel
        , text "rperm  =" <+> text (show perm)
        , text "rps    =" <+> text (show ps)
        ]

-- | Entry point from @Interaction.MakeCase@.
splitClauseWithAbsurd :: SplitClause -> Nat -> TCM (Either SplitError (Either SplitClause Covering))
splitClauseWithAbsurd c x = split' Inductive c (BlockingVar x Nothing)

-- | Entry point from @TypeChecking.Empty@ and @Interaction.BasicOps@.
--   @splitLast CoInductive@ is used in the @refine@ tactics.

splitLast :: Induction -> Telescope -> [NamedArg Pattern] -> TCM (Either SplitError Covering)
splitLast ind tel ps = split ind sc (BlockingVar 0 Nothing)
  where sc = SClause tel (idP $ size tel) ps __IMPOSSIBLE__ Nothing

-- | @split ind splitClause x = return res@
--   splits @splitClause@ at pattern var @x@ (de Bruijn index).
--
--   Possible results @res@ are:
--
--   1. @Left err@:
--      Splitting failed.
--
--   2. @Right covering@:
--      A covering set of split clauses, one for each valid constructor.
--      This could be the empty set (denoting an absurd clause).

split :: Induction
         -- ^ Coinductive constructors are allowed if this argument is
         -- 'CoInductive'.
      -> SplitClause
      -> BlockingVar
      -> TCM (Either SplitError Covering)
split ind sc x = fmap (blendInAbsurdClause (splitDbIndexToLevel sc x)) <$>
    split' ind sc x
  where
    blendInAbsurdClause :: Nat -> Either SplitClause Covering -> Covering
    blendInAbsurdClause n = fromRight (const $ Covering n [])

    splitDbIndexToLevel :: SplitClause -> BlockingVar -> Nat
    splitDbIndexToLevel sc@SClause{ scTel = tel, scPerm = perm } x =
      dbIndexToLevel tel perm $ blockingVarNo x

-- | Convert a de Bruijn index relative to a telescope to a de Buijn level.
--   The result should be the argument (counted from left, starting with 0)
--   to split at (dot patterns included!).
dbIndexToLevel :: Telescope -> Permutation -> Int -> Nat
dbIndexToLevel tel perm x = if n < 0 then __IMPOSSIBLE__ else n
  where n = if k < 0
            then __IMPOSSIBLE__
            else case permute perm [0..] !!! k of
                   Nothing -> __IMPOSSIBLE__
                   Just n  -> n
        k = size tel - x - 1

-- | @split' ind splitClause x = return res@
--   splits @splitClause@ at pattern var @x@ (de Bruijn index).
--
--   Possible results @res@ are:
--
--   1. @Left err@:
--      Splitting failed.
--
--   2. @Right (Left splitClause')@:
--      Absurd clause (type of @x@ has 0 valid constructors).
--
--   3. @Right (Right covering)@:
--      A covering set of split clauses, one for each valid constructor.

split' :: Induction
          -- ^ Coinductive constructors are allowed if this argument is
          -- 'CoInductive'.
       -> SplitClause
       -> BlockingVar
       -> TCM (Either SplitError (Either SplitClause Covering))
split' ind sc@(SClause tel perm ps _ target) (BlockingVar x mcons) = liftTCM $ runExceptionT $ do

  debugInit tel perm x ps

  -- Split the telescope at the variable
  -- t = type of the variable,  Δ₁ ⊢ t
  (n, t, delta1, delta2) <- do
    let (tel1, Dom info (n, t) : tel2) = genericSplitAt (size tel - x - 1) $ telToList tel
    return (n, Dom info t, telFromList tel1, telFromList tel2)

  -- Compute the one hole context of the patterns at the variable
  (hps, hix) <- do
    let holes = reverse $ permute perm $ zip [0..] $ allHolesWithContents ps
    unless (length holes == length (telToList tel)) $
      fail "split: bad holes or tel"

    -- There is always a variable at the given hole.
    let (hix, (VarP s, hps)) = case holes !!! x of
                                 Nothing -> __IMPOSSIBLE__
                                 Just p  -> p
    debugHoleAndType delta1 delta2 s hps t

    return (hps, hix)

  -- Check that t is a datatype or a record
  -- Andreas, 2010-09-21, isDatatype now directly throws an exception if it fails
  -- cons = constructors of this datatype
  (d, pars, ixs, cons) <- inContextOfT $ isDatatype ind t

  -- Compute the neighbourhoods for the constructors
  ns <- catMaybes <$> do
    forM cons $ \ con ->
      fmap (con,) <$> do
        msc <- computeNeighbourhood delta1 n delta2 perm d pars ixs hix hps con
        Trav.forM msc $ \ sc -> lift $ snd <$> fixTarget sc{ scTarget = target }

  case ns of
    []  -> do
      let absurd = VarP "()"
      return $ Left $ SClause
               { scTel  = telFromList $ telToList delta1 ++
                                        [fmap ((,) "()") t] ++ -- add name "()"
                                        telToList delta2
               , scPerm = perm
               , scPats = plugHole absurd hps
               , scSubst = idS -- not used anyway
               , scTarget = Nothing -- not used
               }

    -- Andreas, 2011-10-03
    -- if more than one constructor matches, we cannot be irrelevant
    -- (this piece of code is unreachable if --experimental-irrelevance is off)
    (_ : _ : _) | unusableRelevance (getRelevance t) ->
      throwException . IrrelevantDatatype =<< do liftTCM $ buildClosure (unDom t)

  -- Andreas, 2012-10-10 fail if precomputed constructor set does not cover
  -- all the data type constructors

    _ | Just pcons' <- mcons,
        let pcons = map conName pcons',
        let cons = (map fst ns),
        let diff = Set.fromList cons Set.\\ Set.fromList pcons,
        not (Set.null diff) -> do
          liftTCM $ reportSDoc "tc.cover.precomputed" 10 $ vcat
            [ hsep $ text "pcons =" : map prettyTCM pcons
            , hsep $ text "cons  =" : map prettyTCM cons
            ]
          throwException (GenericSplitError "precomputed set of constructors does not cover all cases")

    _  -> return $ Right $ Covering xDBLevel ns

  where
    xDBLevel :: Nat
    xDBLevel = dbIndexToLevel tel perm x

    inContextOfT :: MonadTCM tcm => tcm a -> tcm a
    inContextOfT = addCtxTel tel . escapeContext (x + 1)

    inContextOfDelta2 :: MonadTCM tcm => tcm a -> tcm a
    inContextOfDelta2 = addCtxTel tel . escapeContext x

    -- Debug printing
    debugInit tel perm x ps =
      liftTCM $ reportSDoc "tc.cover.top" 10 $ vcat
        [ text "TypeChecking.Coverage.split': split"
        , nest 2 $ vcat
          [ text "tel     =" <+> prettyTCM tel
          , text "perm    =" <+> text (show perm)
          , text "x       =" <+> text (show x)
          , text "ps      =" <+> text (show ps)
          ]
        ]

    debugHoleAndType delta1 delta2 s hps t =
      liftTCM $ reportSDoc "tc.cover.top" 10 $ nest 2 $ vcat $
        [ text "p      =" <+> text (patVarNameToString s)
        , text "hps    =" <+> text (show hps)
        , text "delta1 =" <+> prettyTCM delta1
        , text "delta2 =" <+> inContextOfDelta2 (prettyTCM delta2)
        , text "t      =" <+> inContextOfT (prettyTCM t)
        ]

-- | @splitResult f sc = return res@
--
--   If the target type of @sc@ is a record type, a covering set of
--   split clauses is returned (@sc@ extended by all valid projection patterns),
--   otherwise @res == Nothing@.
--   Note that the empty set of split clauses is returned if the record has no fields.
splitResult :: QName -> SplitClause -> TCM (Maybe Covering)
splitResult f sc@(SClause tel perm ps _ target) = do
  reportSDoc "tc.cover.split" 10 $ vcat
    [ text "splitting result:"
    , nest 2 $ text "f      =" <+> text (show f)
    , nest 2 $ text "target =" <+> (addContext tel $ maybe empty prettyTCM target)
    ]
  -- if we want to split projections, but have no target type, we give up
  let done = return Nothing
  caseMaybe target done $ \ t -> do
    isR <- addCtxTel tel $ isRecordType $ unArg t
    case isR of
      Just (_r, vs, Record{ recFields = fs }) -> do
        reportSDoc "tc.cover" 20 $ sep
          [ text $ "we are of record type _r = " ++ show _r
          , text   "applied to parameters vs = " <+> (addCtxTel tel $ prettyTCM vs)
          , text $ "and have fields       fs = " ++ show fs
          ]
        fvs <- freeVarsToApply f
        let es = patternsToElims perm ps
        let self  = defaultArg $ Def f (map Apply fvs) `applyE` es
            pargs = vs ++ [self]
        reportSDoc "tc.cover" 20 $ sep
          [ text   "we are              self = " <+> (addCtxTel tel $ prettyTCM $ unArg self)
          ]
        let -- WRONG: -- n = length ps -- past the last argument, is pos. of proj pat.
            -- n = size tel -- past the last variable, is pos. of proj pat. DURING SPLITTING
            n = permRange perm -- Andreas & James, 2013-11-19 includes the dot patterns!
            -- See test/succeed/CopatternsAndDotPatterns.agda for a case with dot patterns
            -- and copatterns which fails for @n = size tel@ with a broken case tree.
        Just . Covering n <$> do
          forM fs $ \ proj -> do
            -- compute the new target
            dType <- defType <$> do getConstInfo $ unArg proj -- WRONG: typeOfConst $ unArg proj
            let -- type of projection instantiated at self
                target' = Just $ proj $> dType `apply` pargs
                sc' = sc { scPats   = scPats sc ++ [fmap (Named Nothing . ProjP) proj]
                         , scSubst  = idS
                         , scTarget = target'
                         }
            return (unArg proj, sc')
      _ -> done

-- * Boring instances

-- | For debugging only.
instance PrettyTCM SplitClause where
  prettyTCM (SClause tel perm pats sigma target) = sep
    [ text "SplitClause"
    , nest 2 $ vcat
      [ text "tel          = " <+> prettyTCM tel
      , text "perm         = " <+> prettyTCM perm
      , text "pats         = " <+> sep (map (prettyTCM . namedArg) pats)
      , text "subst        = " <+> (text . show) sigma
      , text "target       = " <+> do
          caseMaybe target empty $ \ t -> do
            addContext tel $ prettyTCM t
      -- Triggers crash (see Issue 1374).
      -- , text "subst target = " <+> do
      --     caseMaybe target empty $ \ t -> do
      --       addContext tel $ prettyTCM $ applySubst sigma t
      ]
    ]
