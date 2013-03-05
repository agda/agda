{-# LANGUAGE CPP, PatternGuards, FlexibleContexts, TupleSections #-}

module Agda.TypeChecking.Coverage where

import Control.Monad
import Control.Monad.Error
import Control.Applicative
import Data.List
import qualified Data.Set as Set
import Data.Set (Set)

import Agda.Syntax.Position
import Agda.Syntax.Common hiding (Arg,Dom)
import qualified Agda.Syntax.Common as C
import Agda.Syntax.Internal
import Agda.Syntax.Internal.Pattern

import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Monad.Closure
import Agda.TypeChecking.Monad.Trace
import Agda.TypeChecking.Monad.Signature
import Agda.TypeChecking.Monad.Options
import Agda.TypeChecking.Monad.Exception
import Agda.TypeChecking.Monad.Context

import Agda.TypeChecking.Rules.LHS.Problem (FlexibleVar(..),flexibleVarFromHiding)
import Agda.TypeChecking.Rules.LHS.Unify
import Agda.TypeChecking.Rules.LHS.Instantiate
import Agda.TypeChecking.Rules.LHS
import qualified Agda.TypeChecking.Rules.LHS.Split as Split

import Agda.TypeChecking.Coverage.Match
import Agda.TypeChecking.Coverage.SplitTree

import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Primitive (constructorForm)
import Agda.TypeChecking.Telescope
import Agda.TypeChecking.Irrelevance

import Agda.Interaction.Options

import Agda.Utils.Permutation
import Agda.Utils.Size
import Agda.Utils.Tuple
import Agda.Utils.List
import Agda.Utils.Maybe
import Agda.Utils.Monad

#include "../undefined.h"
import Agda.Utils.Impossible

data SplitClause = SClause
      { scTel    :: Telescope      -- ^ Type of variables in @scPats@.
      , scPerm   :: Permutation    -- ^ How to get from the variables in the patterns to the telescope.
      , scPats   :: [Arg Pattern]  -- ^ The patterns leading to the currently considered branch of the split tree.
      , scSubst  :: Substitution   -- ^ Substitution from @scTel@ to old context.
      , scTarget :: Maybe Type     -- ^ The type of the rhs.
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
  , scPats   = clausePats cl
  , scSubst  = __IMPOSSIBLE__
  , scTarget = Nothing
  }

type CoverM = ExceptionT SplitError TCM

{- UNUSED
typeOfVar :: Telescope -> Nat -> Dom Type
typeOfVar tel n
  | n >= len  = __IMPOSSIBLE__
  | otherwise = fmap snd  -- throw away name, keep Arg Type
                  $ ts !! fromIntegral (len - 1 - n)
  where
    len = genericLength ts
    ts  = telToList tel
-}

-- | Old top-level function for checking pattern coverage.
--   DEPRECATED
checkCoverage :: QName -> TCM ()
checkCoverage f = do
  d <- getConstInfo f
  case theDef d of
    Function{ funProjection = Nothing, funClauses = cs@(_:_) } -> do
      coverageCheck f (defType d) cs
      return ()
    Function{ funProjection = Just _ } -> __IMPOSSIBLE__
    _ -> __IMPOSSIBLE__

-- | Top-level function for checking pattern coverage.
coverageCheck :: QName -> Type -> [Clause] -> TCM SplitTree
coverageCheck f t cs = do
  TelV gamma a <- telView t
  let -- n             = arity
      -- lgamma/gamma' = telescope of non-dropped arguments
      -- xs            = variable patterns fitting lgamma
      n            = size gamma
      lgamma       = telToList gamma
      xs           = map (argFromDom . fmap (const $ VarP "_")) $ lgamma
      -- construct the initial split clause
      sc           = SClause gamma (idP n) xs idS $ Just a
{- OLD
  let -- n             = arity
      -- lgamma/gamma' = telescope of non-dropped arguments
      -- xs            = variable patterns fitting lgamma
      n            = genericLength $ clausePats $ head cs
      (lgamma, rgamma) = genericSplitAt n $ telToList gamma
      gamma'       = telFromList lgamma
      xs           = map (argFromDom . fmap (const $ VarP "_")) $ lgamma
      -- construct the initial split clause
      b            = telePi (telFromList rgamma) a
      sc           = SClause gamma' (idP n) xs idS $ Just b
-}
  reportSDoc "tc.cover.top" 10 $ vcat
    [ text "Coverage checking"
    , nest 2 $ vcat $ map (text . show . clausePats) cs
    ]
  -- used = actually used clauses for cover
  -- pss  = uncovered cases
  (splitTree, used, pss) <- cover cs sc
  reportSDoc "tc.cover.splittree" 10 $ vcat
    [ text "generated split tree for" <+> prettyTCM f
    , text $ show splitTree
    ]
  whenM (optCompletenessCheck <$> pragmaOptions) $
    -- report an error if there are uncovered cases
    unless (null pss) $
        setCurrentRange (getRange cs) $
          typeError $ CoverageFailure f pss
  -- is = indices of unreachable clauses
  let is = Set.toList $ Set.difference (Set.fromList [0..genericLength cs - 1]) used
  -- report an error if there are unreachable clauses
  unless (null is) $ do
      let unreached = map (cs !!) is
      setCurrentRange (getRange unreached) $
        typeError $ UnreachableClauses f (map clausePats unreached)
  return splitTree


-- | @cover cs (SClause _ _ ps _) = return (splitTree, used, pss)@.
--   checks that the list of clauses @cs@ covers the given split clause.
--   Returns the @splitTree@, the @used@ clauses, and missing cases @pss@.
cover :: [Clause] -> SplitClause -> TCM (SplitTree, Set Nat, [[Arg Pattern]])
cover cs sc@(SClause tel perm ps _ target) = do
  reportSDoc "tc.cover.cover" 10 $ vcat
    [ text "checking coverage of pattern:"
    , nest 2 $ text "tel  =" <+> prettyTCM tel
    , nest 2 $ text "perm =" <+> text (show perm)
    , nest 2 $ text "ps   =" <+> text (show ps)
    ]
  case match cs ps perm of
    Yes i          -> do
      reportSLn "tc.cover.cover" 10 $ "pattern covered by clause " ++ show i
      -- Check if any earlier clauses could match with appropriate literals
      let is = [ j | (j, c) <- zip [0..i-1] cs, matchLits c ps perm ]
      -- OLD: let is = [ j | (j, c) <- zip [0..] (genericTake i cs), matchLits c ps perm ]
      reportSLn "tc.cover.cover"  10 $ "literal matches: " ++ show is
      return (SplittingDone (size tel), Set.fromList (i : is), [])
    No       -> return (SplittingDone (size tel), Set.empty, [ps])
    Block bs -> do
      reportSLn "tc.cover.strategy" 20 $ "blocking vars = " ++ show bs
      -- xs is a non-empty lists of blocking variables
      -- try splitting on one of them
      xs <- splitStrategy bs tel
      r <- altM1 (split Inductive sc) xs
      case r of
        Left err  -> case err of
          CantSplit c tel us vs _ -> typeError $ CoverageCantSplitOn c tel us vs
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
          (trees, useds, psss) <- unzip3 <$> mapM (cover cs) (map snd scs)
          let tree = SplitAt n $ zipWith (\ (q,_) t -> (q,t)) scs trees
          return (tree, Set.unions useds, concat psss)

splitStrategy :: BlockingVars -> Telescope -> TCM BlockingVars
splitStrategy bs tel = return $ updateLast (mapSnd (const Nothing)) xs
  -- Make sure we do not insists on precomputed coverage when
  -- we make our last try to split.
  -- Otherwise, we will not get a nice error message.
  where
    xs       = bs
{-
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
    Def d args -> do
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
        Record{recPars = np, recCon = c} ->
          return (d, args, [], [c])
        _ -> throw NotADatatype
    _ -> throw NotADatatype

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
computeNeighbourhood :: Telescope -> String -> Telescope -> Permutation -> QName -> Args -> Args -> Nat -> OneHolePatterns -> QName -> CoverM [SplitClause]
computeNeighbourhood delta1 n delta2 perm d pars ixs hix hps con = do

  -- Get the type of the datatype
  dtype <- liftTCM $ (`piApply` pars) . defType <$> getConstInfo d

  -- Get the real constructor name
  Con con [] <- liftTCM $ ignoreSharing <$> (constructorForm =<< normalise (Con con []))

  -- Get the type of the constructor
  ctype <- liftTCM $ defType <$> getConstInfo con

  -- Lookup the type of the constructor at the given parameters
  (gamma0, cixs) <- do
    TelV gamma0 (El _ d) <- liftTCM $ telView (ctype `piApply` pars)
    let Def _ cixs = ignoreSharing d
    return (gamma0, cixs)

  -- Andreas, 2012-02-25 preserve name suggestion for recursive arguments
  -- of constructor

  let preserve (x, t@(El _ (Def d' _))) | d == d' = (n, t)
      preserve (x, (El s (Shared p))) = preserve (x, El s $ derefPtr p)
      preserve p = p
      gammal = map (fmap preserve) . telToList $ gamma0
      gamma  = telFromList gammal

  debugInit con ctype pars ixs cixs delta1 delta2 gamma hps hix

  -- All variables are flexible
  -- let flex = [0..size delta1 + size gamma - 1]
  let gammaDelta1  = gammal ++ telToList delta1
      makeFlex i d = flexibleVarFromHiding (getHiding d) i
      flex = zipWith makeFlex [0 .. size gammaDelta1 - 1] gammaDelta1

  -- Unify constructor target and given type (in Δ₁Γ)
  let conIxs   = drop (size pars) cixs
      givenIxs = raise (size gamma) ixs

  r <- addCtxTel (delta1 `abstract` gamma) $
       unifyIndices flex (raise (size gamma) dtype) conIxs givenIxs

  case r of
    NoUnify _ _ _ -> do
      debugNoUnify
      return []
    DontKnow _    -> do
      debugCantSplit
      throwException $ CantSplit con (delta1 `abstract` gamma) conIxs givenIxs
                                 (map (var . flexVar) flex)
    Unifies sub   -> do
      debugSubst "sub" sub

      -- Substitute the constructor for x in Δ₂: Δ₂' = Δ₂[conv/x]
      let conv    = Con con  $ teleArgs gamma   -- Θ Γ ⊢ conv (for any Θ)
          delta2' = subst conv $ raiseFrom 1 (size gamma) delta2
      debugTel "delta2'" delta2'

      -- Compute a substitution ρ : Δ₁ΓΔ₂' → Δ₁(x:D)Δ₂'
      let rho = liftS (size delta2') $ conv :# raiseS (size gamma)
             --    [ Var i [] | i <- [0..size delta2' - 1] ]
             -- ++ [ raise (size delta2') conv ]
             -- ++ [ Var i [] | i <- [size delta2' + size gamma ..] ]

      -- Plug the hole with the constructor and apply ρ
      -- TODO: Is it really correct to use Nothing here?
      let conp = ConP con Nothing $ map (fmap VarP) $ teleArgNames gamma
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

      return [SClause theta' rperm rps rsub Nothing] -- target fixed later

  where
    debugInit con ctype pars ixs cixs delta1 delta2 gamma hps hix =
      liftTCM $ reportSDoc "tc.cover.split.con" 20 $ vcat
        [ text "computeNeighbourhood"
        , nest 2 $ vcat
          [ text "con    =" <+> prettyTCM con
          , text "ctype  =" <+> prettyTCM ctype
          , text "hps    =" <+> text (show hps)
          , text "pars   =" <+> prettyList (map prettyTCM pars)
          , text "ixs    =" <+> addCtxTel (delta1 `abstract` gamma) (prettyList (map prettyTCM ixs))
          , text "cixs   =" <+> prettyList (map prettyTCM cixs)
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
--   @Abs@ is for absurd clause.
splitClauseWithAbs :: Clause -> Nat -> TCM (Either SplitError (Either SplitClause Covering))
splitClauseWithAbs c x = split' Inductive (clauseToSplitClause c) (x, Nothing)

-- | Entry point from @TypeChecking.Empty@ and @Interaction.BasicOps@.
splitLast :: Induction -> Telescope -> [Arg Pattern] -> TCM (Either SplitError Covering)
splitLast ind tel ps = split ind sc (0, Nothing)
  where sc = SClause tel (idP $ size tel) ps __IMPOSSIBLE__ Nothing

-- | @split _ Δ π ps x@. FIXME: Δ ⊢ ps, x ∈ Δ (deBruijn index)
split :: Induction
         -- ^ Coinductive constructors are allowed if this argument is
         -- 'CoInductive'.
      -> SplitClause
      -> BlockingVar
      -> TCM (Either SplitError Covering)
split ind sc x = fmap (blendInAbsurdClause (splitDbIndexToLevel sc x)) <$>
   split' ind sc x
{- OLD
split ind sc@SClause{ scTel = tel, scPerm = perm, scPats = ps } x =
  r <- split' ind sc x
  return $ case r of
    Left err        -> Left err
    Right (Left _)  -> Right $ Covering (dbIndexToLevel tel perm $ fst x) []
    Right (Right c) -> Right c
-}

blendInAbsurdClause :: Nat -> Either SplitClause Covering -> Covering
blendInAbsurdClause n = either (const $ Covering n []) id

splitDbIndexToLevel :: SplitClause -> BlockingVar -> Nat
splitDbIndexToLevel sc@SClause{ scTel = tel, scPerm = perm } x =
  dbIndexToLevel tel perm $ fst x

-- | Convert a de Bruijn index relative to a telescope to a de Buijn level.
--   The result should be the argument (counted from left, starting with 0)
--   to split at (dot patterns included!).
dbIndexToLevel tel perm x = if n < 0 then __IMPOSSIBLE__ else n
  where n = permute perm [0..] !! (size tel - x - 1)

split' :: Induction
          -- ^ Coinductive constructors are allowed if this argument is
          -- 'CoInductive'.
       -> SplitClause
       -> BlockingVar
       -> TCM (Either SplitError (Either SplitClause Covering))
split' ind sc@(SClause tel perm ps _ target) (x, mcons) = liftTCM $ runExceptionT $ do

  debugInit tel perm x ps

  -- Split the telescope at the variable
  -- t = type of the variable,  Δ₁ ⊢ t
  (n, t, delta1, delta2) <- do
    let (tel1, C.Dom info (n, t) : tel2) = genericSplitAt (size tel - x - 1) $ telToList tel
    return (n, C.Dom info t, telFromList tel1, telFromList tel2)

  -- Compute the one hole context of the patterns at the variable
  (hps, hix) <- do
    let holes = reverse $ permute perm $ zip [0..] $ allHolesWithContents ps
    unless (length holes == length (telToList tel)) $
      fail "split: bad holes or tel"

    -- There is always a variable at the given hole.
    let (hix, (VarP s, hps)) = holes !! x
    debugHoleAndType delta1 delta2 s hps t

    return (hps, hix)

  -- Check that t is a datatype or a record
  -- Andreas, 2010-09-21, isDatatype now directly throws an exception if it fails
  -- cons = constructors of this datatype
  (d, pars, ixs, cons) <- inContextOfT $ isDatatype ind t

  liftTCM $ whenM (optWithoutK <$> pragmaOptions) $
    inContextOfT $ Split.wellFormedIndices (unDom t)

  -- Compute the neighbourhoods for the constructors
  ns <- concat <$> do
    forM cons $ \ con ->
      map (con,) <$> do
        mapM fixTarget =<<
          computeNeighbourhood delta1 n delta2 perm d pars ixs hix hps con
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

    _ | Just pcons <- mcons,
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
    xDBLevel = dbIndexToLevel tel perm x

    -- update the target type, add more patterns to split clause
    -- if target becomes a function type.
    fixTarget :: SplitClause -> CoverM SplitClause
    fixTarget sc@SClause{ scSubst = sigma } =
      flip (maybe $ return sc) target $ \ a -> do
        TelV tel b <- lift $ telView $ applySubst sigma a
        let n      = size tel
            lgamma = telToList tel
            xs     = map (argFromDom . fmap (const $ VarP "_")) $ lgamma
        if (n == 0) then return sc { scTarget = Just b }
         else return $ SClause
          { scTel    = telFromList $ telToList (scTel sc) ++ lgamma
          , scPerm   = liftP n $ scPerm sc
          , scPats   = scPats sc ++ xs
          , scSubst  = liftS n $ sigma
          , scTarget = Just b
          }

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
        [ text "p      =" <+> text s
        , text "hps    =" <+> text (show hps)
        , text "delta1 =" <+> prettyTCM delta1
        , text "delta2 =" <+> inContextOfDelta2 (prettyTCM delta2)
        , text "t      =" <+> inContextOfT (prettyTCM t)
        ]
