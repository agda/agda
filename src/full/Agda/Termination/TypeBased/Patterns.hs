{- | Contains functions that are used to encode clause patterns
     Pattern encoding is very important step of the type-based termination, since it allows to populate the set of rigid variables.

     Here and after, the implementation heavily refers to the notion of _cluster_.
     Given a sized signature of a function, clusters are defined as indexes of all size variables in that signature.
     Example:
     If a function foo has type 't₀ → t₁<ε₁,t₂> → t₃', then the clusters are [0, 1, 2, 3].

     Clusters represent all possible size parameters of a function (even codomain is used, it has its role in coinductive definitions).
     Clusters are needed to represent the handling of non-recursive constructors, constructing size-change-termination matrices,
     and applying certain heuristic during the graph processing phase.
-}
module Agda.Termination.TypeBased.Patterns
  ( matchPatterns
  ) where

import Control.Monad ( when, forM )
import Control.Monad.Trans ( MonadTrans(lift) )
import Control.Monad.Trans.State ( StateT(runStateT), gets, modify )
import Data.Foldable (traverse_)
import qualified Data.IntMap as IntMap
import Data.IntMap ( IntMap )
import qualified Data.List as List
import qualified Data.List.NonEmpty as NonEmpty
import Data.List.NonEmpty (NonEmpty (..))

import Agda.Syntax.Abstract.Name ( QName )
import Agda.Syntax.Common ( Named(Named, namedThing), Arg(Arg, unArg) )
import Agda.Syntax.Internal ( QName, DeBruijnPattern, DBPatVar(dbPatVarIndex, dbPatVarName),  Pattern'(DefP, ProjP, VarP, ConP, DotP, LitP, IApplyP), NAPs, ConHead(conName) )
import Agda.Termination.Monad ( isCoinductiveProjection )
import Agda.Termination.TypeBased.Common ( applyDataType, getDatatypeParametersByConstructor, updateSizeVariables )
import Agda.Termination.TypeBased.Syntax ( SizeSignature(SizeSignature), SizeBound(..), FreeGeneric(FreeGeneric), SizeType(..), Size(..), pattern UndefinedSizeType, sizeCodomain )
import Agda.Termination.TypeBased.Monad ( getCurrentRigids, getRootArity, requestNewRigidVariable, appendCoreVariable, TBTM, recordError )
import Agda.TypeChecking.Monad.Base ( Definition(defSizedType, defType, defCopy), MonadTCM(liftTCM) )
import Agda.TypeChecking.Monad.Debug ( reportSDoc )
import Agda.TypeChecking.Monad.Signature ( HasConstInfo(getConstInfo) )
import Agda.TypeChecking.Pretty ( PrettyTCM(prettyTCM), pretty, nest, (<+>), vcat, text )
import Agda.TypeChecking.Polarity.Base ( Polarity(Contravariant, Covariant) )
import Agda.Utils.Impossible ( __IMPOSSIBLE__ )
import Agda.Utils.List ((!!!), initWithDefault)
import Agda.Utils.Singleton ( Singleton(singleton) )
import Agda.Utils.List1 ( appendList )

type PatternEncoder a = StateT PatternEnvironment TBTM a

data PatternEnvironment = PatternEnvironment
  { peDepth         :: Int
  -- ^ Current depth of the pattern.
  , peDepthStack    :: IntMap (NonEmpty Int)
  -- ^ A map from cluster to a stack of depth variables
  , peCoDepth       :: Int
  -- ^ Current depth of the codomain. This is relevant in the case of copattern matching of a coinductive definition.
  --   This is basically the same depth stack as @peDepth@, but we refer to this one as @coDepth@ to avoid confusion.
  , peCoDepthStack  :: [Int]
  -- ^ A stack of depth variables for copattern matching.
  }


-- | This function populates the set of rigid variables for a clause.
--
--   During the processing of a parameter, we maintain a stack of depth size variables,
--   which get assigned to core variables on the corresponding levels of decomposition.
--   Consider the following example:
--
--     data T : Set where
--       c1 : T -> T -> T -> T
--       c2 : T -> T
--
--   Assume that there is a parameter `(x : T)` which has size t₀. If a corresponding pattern looks like `c1 a b (c2 c)`,
--   then `a` is assigned to a variable t₁, `b` is assigned to a variable t₁, and `c` is assigned to a variable t₂, where t₂ < t₁ < t₀
--   In this case, t₀ has depth 0, t₁ has depth 1, and t₂ has depth 2.
--   We can see that `a` and `b` has the same depth variable. The algorithm indeed assigns the same depth variable to all core variables on the same level.
--   The motivation is that the least upper bound for `a` and `b` in this case is t₁. If the size variables were different, the least upper bound would be t₀.
--
--   Returns the variables at the lowest level of each cluster and expected size type of clause
matchPatterns :: SizeType -> NAPs -> TBTM ([Int], SizeType)
matchPatterns tele patterns = do
  (sizeTypeOfClause, modifiedState) <- runStateT (matchLHS tele patterns) (PatternEnvironment
    { peDepth = 0
    , peDepthStack = IntMap.empty
    , peCoDepth = 0
    , peCoDepthStack = []
    })
  currentRootArity <- getRootArity
  let finalLeaves = peDepthStack modifiedState
  let leafVariables = map (\i -> case IntMap.lookup i finalLeaves of
        Just l -> NonEmpty.last l
        _ -> -1
        ) [0..currentRootArity - 1]
  pure (leafVariables, sizeTypeOfClause)

-- Matches LHS of a clause, processing patterns and copatterns
matchLHS :: SizeType -> NAPs -> PatternEncoder (SizeType)
matchLHS tele patterns = do
  -- First, we try to match all application patterns against the expected type
  restPatterns <- foldDomainSizeType
    (\args i (Arg _ (Named _ pat)) -> case pat of
      VarP pi v -> do
        reportSDoc "term.tbt" 20 $ "Assigning" <+> text (dbPatVarName v) <+> "to" <+> (pretty (FreeGeneric args i))
        lift $ appendCoreVariable (dbPatVarIndex v) (Left $ FreeGeneric args i)
      DotP _ term -> pure ()
      _ -> __IMPOSSIBLE__
      )
    (\sizeType (Arg _ (Named _ pat)) -> do
      -- We are trying to match a regular constructor-built pattern
      initializeLeafVars sizeType
      matchSizePattern pat sizeType)
      patterns tele
  let fallback = applyDataType (replicate (length patterns) UndefinedSizeType) tele
  case restPatterns of
    [] ->
        -- No projection, we can exit pattern matching
        pure fallback
    (p : ps) -> case p of
      (Arg _ (Named _ (ProjP _ qn))) -> do
        -- Since it is a projection, the matched type must be a record, i.e. a size tree.
        let (_, codom) = sizeCodomain tele
        let SizeTree _ coPrincipal recordArgs = codom
        constInfo <- getConstInfo qn
        let sig@(SizeSignature bounds tele) = defSizedType constInfo

        isForCoinduction <- do
          coinductiveProjection <- isCoinductiveProjection True qn
          when coinductiveProjection $ initializeCopatternProjection coPrincipal
          pure coinductiveProjection

        currentCoDepth <- gets peCoDepth
        let newCoDepth = if isForCoinduction then (currentCoDepth + 1)                else currentCoDepth
        newCodepthVar <- if isForCoinduction then (getOrRequestCoDepthVar newCoDepth) else pure (-1)

        freshenedSignature <- freshenCopatternProjection newCodepthVar bounds tele
        -- Additional argument is needed because we want to get rid of the principal argument in the signature
        -- This is application that is intended to get rid of the basic record arguments
        let appliedProjection = case codom of
              UndefinedSizeType -> UndefinedSizeType
              _ -> applyDataType ((map snd recordArgs) ++ [UndefinedSizeType]) freshenedSignature
        -- TODO: handle copying here,
        -- since apparently there can be copies in copatterns (!)
        when (defCopy constInfo) $ lift $ recordError "Copy in a copattern projection"
        reportSDoc "term.tbt" 20 $ vcat $
          [ "Matching copattern projection:" <+> prettyTCM qn] ++ map (nest 2)
          [ "coinductive: " <+> text (show isForCoinduction)
          , "of core type: " <+> prettyTCM (defType constInfo)
          , "of type: " <+> pretty appliedProjection
          ]
        reportSDoc "term.tbt" 60 $ vcat $ map (nest 2)
          [ "of full sized type: " <+> pretty sig
          , "of bounds: " <+> pretty bounds
          , "with record arguments: " <+> pretty recordArgs
          , "of freshened signature: " <+> pretty freshenedSignature
          , "copy: " <+> pretty (defCopy constInfo)
          , "new codepth: " <+> text (show newCoDepth)
          ]
        modify (\s -> s { peCoDepth = newCoDepth })
        -- Attempt regular pattern matching again, because decomposed projection may have own parameters
        matchLHS appliedProjection ps
      _ ->
        -- Might be the case of large elimination
        pure fallback

-- | Input: a size type, that is located in domain
-- Sets up root sizes for all first-order size variables in the domain
initializeLeafVars :: SizeType -> PatternEncoder ()
initializeLeafVars (SizeTree size _ ts) = do
  case size of
    SUndefined -> pure ()
    SDefined i -> modify ( \s -> s
      { peDepthStack = IntMap.insert i (singleton i) (peDepthStack s)
      , peDepth = 0
      })
  traverse_ (initializeLeafVars . snd) ts
initializeLeafVars (SizeGenericVar _ _) = pure ()
initializeLeafVars (SizeArrow _ r) = initializeLeafVars r
initializeLeafVars (SizeGeneric _ r) = initializeLeafVars r

-- | Sets up the data for coinductive copattern matching
initializeCopatternProjection :: Size -> PatternEncoder ()
initializeCopatternProjection (SDefined i) = do
    currentCodepthStack <- gets peCoDepthStack
    case currentCodepthStack of
        [] -> modify (\s -> s { peCoDepthStack = [i] })
        _ -> pure () -- It means that the codepth stack is already initialized
initializeCopatternProjection _ = pure () -- If there is no sized principal argument, then there is nothing to initialize

-- Matches the pattern, populating the set of core and rigid variables.
-- We need to consider both cluster and depth when choosing the variable to split,
-- otherwise we may accidentally introduce a size that belongs to a wrong cluster.
matchSizePattern :: DeBruijnPattern -> SizeType -> PatternEncoder ()
matchSizePattern (VarP pi v) expected = do
  reportSDoc "term.tbt" 20 $ "Assigning" <+> text (dbPatVarName v) <+> "to" <+> pretty expected
  lift $ appendCoreVariable (dbPatVarIndex v) (Right expected)
matchSizePattern p@(ConP hd pi args) expected = do
  reportSDoc "term.tbt" 20 $ "Matching pattern " <+> prettyTCM p <+> "with expected type" <+> pretty expected
  let cn = conName hd
  ci <- getConstInfo cn
  let sizeSig = defSizedType ci
  -- We still need to populate core variables for the completeness of the checking
  let defaultAction = traverse_ (\pat -> withDepth (-1) $ matchSizePattern (namedThing $ unArg pat) UndefinedSizeType) args
  case (expected) of
    UndefinedSizeType -> defaultAction
    SizeTree size _ ts -> do
      rigids <- lift getCurrentRigids
      let cluster = case size of
            SDefined idx -> getCluster rigids idx
            SUndefined -> -1
      depth <- gets peDepth
      currentCodomainVar <- getOrRequestDepthVar cluster depth
      -- We are going to request the depth var lazily
      let innerVar = getOrRequestDepthVar cluster (depth + 1)
      refreshedConstructor <- freshenPatternConstructor cn currentCodomainVar innerVar expected sizeSig
      reportSDoc "term.tbt" 20 $ vcat $ map (nest 2)
        [ "Pattern constructor name: " <+> (prettyTCM cn)
        , "Refreshed constructor type: " <+> pretty refreshedConstructor
        , "expected: " <+> pretty expected
        ]
      reportSDoc "term.tbt" 60 $ vcat $ map (nest 2)
        [ "level variable of current datatype:" <+> text (show currentCodomainVar)
        , "raw signature of constructor: " <+> pretty sizeSig
        , "depth: " <+> text (show depth)
        ]

      let (_, codomain) = sizeCodomain refreshedConstructor
      case codomain of
        SizeTree _ _ realArgs -> lift $ ensurePatternIntegrity (map snd realArgs) (map snd ts)
        _ -> pure ()
      _ <- foldDomainSizeType
        (\args i pat -> withDepth (-1) $ matchSizePattern pat UndefinedSizeType)
        (\size pat -> do
          argCluster <- lift $ getClusterByTele size
          depth <- gets peDepth
          let newDepth = if argCluster == cluster && argCluster /= -1 then (depth + 1) else 0
          reportSDoc "term.tbt" 40 $ "About to match:" <+> "pat: " <+> prettyTCM pat <+> ", against" <+> pretty size
          withDepth newDepth $ matchSizePattern pat size)
        (map (namedThing . unArg) args)
        refreshedConstructor
      pure ()
    _ -> lift $ recordError "Unsupported pattern matching"
matchSizePattern (DotP pi _) _ = return ()
matchSizePattern (LitP _ _) _ = pure ()
matchSizePattern (ProjP _ _) _ = pure ()
matchSizePattern (IApplyP _ _ _ _) _ = pure ()
matchSizePattern (DefP _ _ _) _ = __IMPOSSIBLE__ -- cubical agda is not supported, this place should not be reachable as it is filtered out earlier

-- | Runs action with the specified inductive depth
withDepth :: Int -> PatternEncoder a -> PatternEncoder a
withDepth i action = do
  oldState <- gets peDepth
  modify (\s -> s { peDepth = i })
  res <- action
  modify (\s -> s { peDepth = oldState })
  pure res

-- | Folding on size telescope zipped with a supplied list values
foldDomainSizeType :: Monad m => (Int -> Int -> b -> m a) -> (SizeType -> b -> m a) -> [b] -> SizeType -> m [b]
foldDomainSizeType = foldDomainSizeType' 0

foldDomainSizeType' :: Monad m => Int -> (Int -> Int -> b -> m a) -> (SizeType -> b -> m a) -> [b] -> SizeType -> m [b]
foldDomainSizeType' c f1 f2 (b : bs) (SizeArrow l r) = do
  ofDomain <- f2 l b
  foldDomainSizeType' c f1 f2 bs r
foldDomainSizeType' c f1 f2 (b : bs) (SizeGeneric args r) = do
  ofDomain <- f1 args c b
  foldDomainSizeType' (c + 1) f1 f2 bs r
foldDomainSizeType' _ _ _ rest _ = pure rest

-- | 'getOrRequestDepthVar cluster level' returns a variable on depth 'level' corresponding to a cluster 'cluster'
getOrRequestDepthVar :: Int -> Int -> PatternEncoder Int
getOrRequestDepthVar cluster level = do
  reportSDoc "term.tbt" 70 $ "Requesting new var of level" <+> text (show level) <+> "for cluster" <+> text (show cluster)
  currentLeaves <- IntMap.lookup cluster <$> gets peDepthStack
  case currentLeaves of
    Nothing -> pure (-1)
    Just currentLeaves -> do
      if (length currentLeaves /= level)
      then
        -- We are requesting a variable from the earlier levels
        pure $ currentLeaves NonEmpty.!! level
      else do
        -- We need to populate a depth stack with a new level
        let actualBound = if ((NonEmpty.head currentLeaves) == -1) then SizeUnbounded else SizeBounded (NonEmpty.last currentLeaves)
        var <- lift $ requestNewRigidVariable Covariant actualBound
        modify (\s -> s { peDepthStack = IntMap.insert cluster (appendList currentLeaves [var]) (peDepthStack s) })
        pure var

-- | Retrieves a new depth variable to reflect a descend in copattern projection
getOrRequestCoDepthVar :: Int -> PatternEncoder Int
getOrRequestCoDepthVar depth = do
  currentCodepthStack <- gets peCoDepthStack
  case (currentCodepthStack !!! depth) of
    Nothing -> do
      let actualBound = if depth == 0 then SizeUnbounded else SizeBounded (currentCodepthStack List.!! (depth - 1))
      var <- lift $ requestNewRigidVariable Contravariant actualBound
      reportSDoc "term.tbt" 70 $ "Requesting new var of codepth" <+> text (show depth) <+> "which is " <+> text (show var)
      modify (\s -> s { peCoDepthStack = peCoDepthStack s ++ [var] })
      pure var
    Just i -> pure i

-- | 'freshenPatternConstructor conName codomainDataVar domainDataVar expectedCodomain sig' decomposes inferred constructor type ('sig')
-- in accordance with the expected data type ('expectedCodomain') type.
-- The decomposed constructor has 'codomainDataVar' as the size variable of its domain
-- and 'domainDataVar' as the size variables of its recursive domains.
freshenPatternConstructor :: QName -> Int -> PatternEncoder Int -> SizeType -> SizeSignature -> PatternEncoder SizeType
freshenPatternConstructor conName codomainDataVar domainDataVar expectedCodomain (SizeSignature bounds constructorType) = do
  let (SizeTree topSize coTopSize datatypeParameters) = expectedCodomain
  let croppedBounds = if codomainDataVar == -1 then bounds else initWithDefault [] bounds
  let shouldBeUnbounded b = b == SizeUnbounded || codomainDataVar == (-1)
  -- We need to strip the codomain size from the constructor here to not introduce weird rigid in the context
  -- It is important to call `domainDataVar` lazily,
  -- because otherwise leaf variables would gain access to a cluster var with lower level than expected
  domainVar <- if all shouldBeUnbounded bounds then pure (-1) else domainDataVar
  newVars <- forM croppedBounds $ \bound -> if shouldBeUnbounded bound then lift $ requestNewRigidVariable Covariant SizeUnbounded else pure domainVar
  reportSDoc "term.tbt" 70 $ vcat
    [ "New variables for instantiation: " <+> text (show newVars)
    , "Bounds: " <+> pretty bounds
    , "modified type: " <+> pretty constructorType
    , "Datatype arguments:" <+> pretty datatypeParameters
    ]
  let augmentedBounds = newVars ++ (if null bounds then [] else [codomainDataVar])
  let instantiatedSig = updateSizeVariables (\i -> augmentedBounds List.!! i) constructorType
  reportSDoc "term.tbt" 70 $ "Instantiated signature: " <+> pretty instantiatedSig
  numberOfArguments <- liftTCM $ getDatatypeParametersByConstructor conName
  reportSDoc "term.tbt" 70 $ "Number of arguments: " <+> text (show numberOfArguments)
  let partialConstructorType = applyDataType (take numberOfArguments $ map snd datatypeParameters) instantiatedSig
  return partialConstructorType

freshenCopatternProjection :: Int -> [SizeBound] -> SizeType -> PatternEncoder SizeType
freshenCopatternProjection newCoDepthVar bounds tele = do
  let isNewPatternSizeVar b = b == SizeUnbounded || newCoDepthVar == (-1)
  newVars <- forM bounds $ \bound -> if isNewPatternSizeVar bound then lift $ requestNewRigidVariable Contravariant SizeUnbounded else pure newCoDepthVar
  reportSDoc "term.tbt" 70 $ "Raw size type of copattern projection: " <+> pretty tele <+> "With new variabless:" <+> text (show newVars)
  let instantiatedSig = updateSizeVariables (newVars List.!!) tele
  pure instantiatedSig

-- This is a protection against postulated univalence.
-- Normally, there cannot be any relation between a size variable and a generic,
-- but introducing univalence there can actually be a relation between them.
ensurePatternIntegrity :: [SizeType] -> [SizeType] -> TBTM ()
ensurePatternIntegrity realTypes expectedTypes = do
  let integrityViolation = any (\(realType, expectedType) -> (isGenericVar expectedType) /= (isGenericVar realType)) (zip realTypes expectedTypes)
  when integrityViolation $ recordError "Integrity violation in clause"
  where
    isGenericVar :: SizeType -> Bool
    isGenericVar (SizeGenericVar _ _) = True
    isGenericVar _ = False

-- Extracts cluster of the top-level size expr
getClusterByTele :: SizeType -> TBTM Int
getClusterByTele (SizeTree (SDefined i) _ _) = do
  ctx <- getCurrentRigids
  pure $ getCluster ctx i
getClusterByTele (SizeArrow _ r) = getClusterByTele r
getClusterByTele (SizeGeneric _ r) = getClusterByTele r
getClusterByTele _ = pure (-1)

-- for a pattern size variable, gets its cluster index
getCluster :: [(Int, SizeBound)] -> Int -> Int
getCluster bounds i = case List.lookup i bounds of
  Nothing -> -1
  Just SizeUnbounded -> i
  Just (SizeBounded j) -> getCluster bounds j
