{- | Contains functions that are used to encode clause patterns
     Pattern encoding is very important step of the type-based termination, since it allows to populate the set of rigid variables.
-}
module Agda.Termination.TypeBased.Patterns where

import Agda.Syntax.Internal.Pattern
import Agda.Termination.TypeBased.Syntax
import Control.Monad.Trans.State
import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Monad.Statistics
import Agda.TypeChecking.Monad.Debug
import Agda.TypeChecking.Monad.Signature
import Agda.Syntax.Common
import qualified Data.Map as Map
import Data.Map ( Map )
import qualified Data.IntMap as IntMap
import Data.IntMap ( IntMap )
import qualified Data.IntSet as IntSet
import Data.IntSet ( IntSet )
import qualified Data.Set as Set
import Data.Set ( Set )
import qualified Data.List as List
import Agda.Syntax.Abstract.Name
import Control.Monad.IO.Class
import Control.Monad.Trans
import Agda.TypeChecking.Monad.Env
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Monad.Context
import Agda.TypeChecking.Telescope
import Agda.Termination.TypeBased.Common
import Agda.TypeChecking.Substitute
import Agda.Termination.TypeBased.Monad
import Agda.TypeChecking.ProjectionLike
import Agda.Utils.Impossible
import Agda.Termination.TypeBased.Checking
import Control.Monad
import Agda.TypeChecking.Pretty
import Debug.Trace
import Agda.Utils.Monad
import Agda.Termination.Common
import Data.Maybe
import Agda.Termination.TypeBased.Encoding
import Agda.Termination.CallGraph
import Agda.Termination.Monad
import Agda.Termination.TypeBased.Graph
import Data.Foldable (traverse_)
import Agda.Utils.List ((!!!))
import Data.Functor ((<&>))
import Agda.Termination.CallMatrix
import qualified Agda.Termination.CallMatrix
import Agda.Utils.Graph.AdjacencyMap.Unidirectional (Edge(..))
import Data.Either
import Agda.Utils.Singleton
import Agda.Termination.Order (Order)
import qualified Agda.Termination.Order as Order
import Agda.Syntax.Internal
import Agda.Syntax.Internal.Pattern

type PatternEncoder a = StateT PatternEnvironment MonadSizeChecker a

data PatternEnvironment = PatternEnvironment
  { peDepth         :: Int
  -- ^ Current depth of the pattern.
  , peDepthStack    :: IntMap [Int]
  -- ^ A map from cluster to a stack of depth variables
  , peCoDepth       :: Int
  -- ^ Current depth of the codomain. This is relevant in the case of copattern matching of a coinductive definition.
  --   This is basically the same depth stack as @peDepth@, but we refer to this one as @coDepth@ to avoid confusion.
  , peCoDepthStack  :: [Int]
  -- ^ A stack of depth variables for copattern matching.
  }


-- | This function populates the set of rigid variables for a clause.
--   Each separate size variable of a function's signature induces a _cluster_,
--   which is an index of a top-level size variable in the function's parameter list.
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
matchPatterns :: SizeTele -> NAPs -> MonadSizeChecker ([Int], SizeTele)
matchPatterns tele patterns = do
  (sizeTypeOfClause, modifiedState) <- runStateT (matchLHS tele patterns) (PatternEnvironment
    { peDepth = 0
    , peDepthStack = IntMap.empty
    , peCoDepth = 0
    , peCoDepthStack = []
    })
  currentRoot <- currentCheckedName
  currentRootArity <- getArity currentRoot
  let finalLeaves = peDepthStack modifiedState
  let leafVariables = map (\i -> case IntMap.lookup i finalLeaves of
        Just l@(_ : _) -> last l
        _ -> -1
        ) [0..currentRootArity - 1]
  pure (leafVariables, sizeTypeOfClause)

-- Matches LHS of a clause, processing patterns and copatterns
matchLHS :: SizeTele -> NAPs -> PatternEncoder (SizeTele)
matchLHS tele patterns = do
  -- First, we try to match all application patterns against the expected type
  restPatterns <- foldDomainSizeTele
    (\args i (Arg _ (Named _ pat)) -> case pat of
      VarP pi v -> do
        reportSDoc "term.tbt" 20 $ "Assigning" <+> text (dbPatVarName v) <+> "to" <+> (text (show (StoredGeneric args i)))
        lift $ appendCoreVariable (dbPatVarIndex v) (StoredGeneric args i)
      DotP _ term -> pure ()
      _ -> __IMPOSSIBLE__
      )
    (\sizeType (Arg _ (Named _ pat)) -> do
      -- We are trying to match a regular constructor-built pattern
      initializeLeafVars sizeType
      matchSizePattern pat sizeType)
      patterns tele
  let fallback = applyDataType (replicate (length patterns) UndefinedSizeTele) tele
  case restPatterns of
    [] ->
        -- No projection, we can exit pattern matching
        pure fallback
    (p : ps) -> case p of
      (Arg _ (Named _ (ProjP _ qn))) -> do
        -- Since it is a projection, the matched type must be a record, i.e. a size tree.
        let (_, (SizeTree principal rest)) = sizeCodomain tele
        constInfo <- getConstInfo qn
        let sizeType = defSizedType constInfo

        case sizeType of
          Nothing -> pure fallback
          Just sig@(SizeSignature bounds contra tele) -> do
            isForCoinduction <- do
              coinductiveProjection <- isCoinductiveProjection True qn
              when coinductiveProjection $ initializeCopatternProjection principal
              pure coinductiveProjection

            currentCoDepth <- gets peCoDepth
            let newCoDepth = if isForCoinduction then (currentCoDepth + 1)                else currentCoDepth
            newCodepthVar <- if isForCoinduction then (getOrRequestCoDepthVar newCoDepth) else pure (-1)

            freshenedSignature <- freshenCopatternProjection newCodepthVar bounds tele
            -- Additional argument is needed because we want to get rid of the principal argument in the signature
            let appliedProjection = applyDataType (rest ++ [UndefinedSizeTele]) freshenedSignature
            reportSDoc "term.tbt" 20 $ vcat
              [ "Entering copattern projection:" <+> prettyTCM qn
              , "Coinductive: " <+> text (show isForCoinduction)
              , "of core type: " <+> prettyTCM (defType constInfo)
              , "of full sized type: " <+> text (show sizeType)
              , "of bounds: " <+> text (show bounds)
              , "rest: " <+> text (show rest)
              , "Freshened signature: " <+> text (show freshenedSignature)
              , "of applied size type: " <+> text (show appliedProjection)
              , "new depth: " <+> text (show newCoDepth)
              ]
            modify (\s -> s { peCoDepth = newCoDepth })
            -- Attempt regular pattern matching again, because decomposed projection may have own parameters
            matchLHS appliedProjection ps
      _ ->
        -- Might be the case of large elimination
        pure fallback

-- | Input: a size type, that is located in domain
-- Sets up root sizes for all first-order size variables in the domain
initializeLeafVars :: SizeTele -> PatternEncoder ()
initializeLeafVars (SizeTree size ts) = do
  case size of
    SUndefined -> pure ()
    SDefined i -> modify ( \s -> s
      { peDepthStack = IntMap.insert i [i] (peDepthStack s)
      , peDepth = 0
      })
  traverse_ initializeLeafVars ts
initializeLeafVars (SizeGenericVar _ _) = pure ()
initializeLeafVars (SizeArrow _ r) = initializeLeafVars r
initializeLeafVars (SizeGeneric _ _ r) = initializeLeafVars r

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
matchSizePattern :: DeBruijnPattern -> SizeTele -> PatternEncoder ()
matchSizePattern (VarP pi v) expected = do
  reportSDoc "term.tbt" 20 $ "Assigning" <+> text (dbPatVarName v) <+> "to" <+> (text (show expected))
  lift $ appendCoreVariable (dbPatVarIndex v) expected
matchSizePattern p@(ConP hd pi args) expected = do
  reportSDoc "term.tbt" 20 $ "Matching pattern " <+> prettyTCM p <+> "with expected type" <+> (text (show expected))
  let cn = conName hd
  ci <- getConstInfo cn
  let sizeSig = defSizedType ci
  -- We still need to populate core variables for the completeness of the checking
  let defaultAction = traverse_ (\pat -> withDepth (-1) $ matchSizePattern (namedThing $ unArg pat) UndefinedSizeTele) args
  case (sizeSig, expected) of
    (Nothing, _) -> defaultAction
    (_, UndefinedSizeTele) -> defaultAction
    (Just sizeSig, SizeTree size ts) -> do
      rigids <- lift getCurrentRigids
      let cluster = case size of
            SDefined idx -> getCluster rigids idx
            SUndefined -> -1
      depth <- gets peDepth
      currentCodomainVar <- getOrRequestDepthVar cluster depth
      -- We are going to request the depth var lazily
      let innerVar = getOrRequestDepthVar cluster (depth + 1)
      reportSDoc "term.tbt" 20 $ "sig:" <+> text (show sizeSig)
      refreshedConstructor <- freshenPatternConstructor cn currentCodomainVar innerVar expected sizeSig
      reportSDoc "term.tbt" 20 $ vcat $ map (nest 2)
        [ "Pattern constructor name: " <+> (prettyTCM cn)
        , "depth: " <+> text (show depth)
        , "level variable of current datatype:" <+> text (show currentCodomainVar)
        , "expected: " <+> text (show expected)
        , "sizeSig: " <+> text (show sizeSig)
        , "Refreshed constructor type: " <+> text (show refreshedConstructor)
        ]

      let (_, codomain) = sizeCodomain refreshedConstructor
      case codomain of
        SizeTree _ realArgs -> lift $ ensurePatternIntegrity realArgs ts
        _ -> pure ()
      _ <- foldDomainSizeTele
        (\args i pat -> withDepth (-1) $ matchSizePattern pat (StoredGeneric args i))
        (\size pat -> do
          argCluster <- lift $ getClusterByTele size
          depth <- gets peDepth
          let newDepth = if argCluster == cluster && argCluster /= -1 then (depth + 1) else 0
          reportSDoc "term.tbt" 20 $ "About to match:" <+> "pat: " <+> prettyTCM pat <+> ", against" <+> text (show size)
          withDepth newDepth $ matchSizePattern pat size)
        (map (namedThing . unArg) args)
        refreshedConstructor
      pure ()
    (_, _) -> trace ("sizeSig: " ++ show sizeSig ++ "expected: " ++ show expected)__IMPOSSIBLE__
matchSizePattern (DotP pi _) _ = return ()
matchSizePattern (LitP _ _) _ = pure ()
matchSizePattern (DefP _ _ _) _ = __IMPOSSIBLE__ -- cubical agda is not supported
matchSizePattern _ _ = __IMPOSSIBLE__

-- | Runs action with the specified inductive depth
withDepth :: Int -> PatternEncoder a -> PatternEncoder a
withDepth i = withStateT (\s -> s { peDepth = i })

-- | Folding on size telescope zipped with a supplied list values
foldDomainSizeTele :: Monad m => (Int -> Int -> b -> m a) -> (SizeTele -> b -> m a) -> [b] -> SizeTele -> m [b]
foldDomainSizeTele f1 f2 (b : bs) (SizeArrow l r) = do
  ofDomain <- f2 l b
  foldDomainSizeTele f1 f2 bs r
foldDomainSizeTele f1 f2 (b : bs) (SizeGeneric args i r) = do
  ofDomain <- f1 args i b
  foldDomainSizeTele f1 f2 bs r
foldDomainSizeTele _ _ rest _ = pure rest

-- | 'getOrRequestDepthVar cluster level' returns a variable on depth 'level' corresponding to a cluster 'cluster'
getOrRequestDepthVar :: Int -> Int -> PatternEncoder Int
getOrRequestDepthVar cluster level = do
  reportSDoc "term.tbt" 20 $ "Requesting new var of level" <+> text (show level) <+> "for cluster" <+> text (show cluster)
  currentLeaves <- IntMap.lookup cluster <$> gets peDepthStack
  case currentLeaves of
    Nothing -> pure (-1)
    Just currentLeaves -> do
      if (length currentLeaves /= level)
      then
        -- We are requesting a variable from the earlier levels
        pure $ currentLeaves List.!! level
      else do
        -- We need to populate a depth stack with a new level
        let actualBound = if (head currentLeaves == -1) then SUndefined else SDefined (last currentLeaves)
        [var] <- lift $ requestNewRigidVariables actualBound [SizeBounded (-1)]
        modify (\s -> s { peDepthStack = IntMap.insert cluster (currentLeaves ++ [var]) (peDepthStack s) })
        pure var

-- | Retrieves a new depth variable to reflect a descend in copattern projection
getOrRequestCoDepthVar :: Int -> PatternEncoder Int
getOrRequestCoDepthVar depth = do
  currentCodepthStack <- gets peCoDepthStack
  case (currentCodepthStack !!! depth) of
    Nothing -> do
      let actualBound = if depth == 0 then SUndefined else SDefined (currentCodepthStack List.!! (depth - 1))
      [var] <- lift $ requestNewRigidVariables actualBound [SizeBounded (-1)]
      reportSDoc "term.tbt" 20 $ "Requesting new var of codepth" <+> text (show depth) <+> "which is " <+> text (show var)
      modify (\s -> s { peCoDepthStack = peCoDepthStack s ++ [var] })
      lift $ recordContravariantSizeVariable var
      pure var
    Just i -> pure i

-- | 'freshenPatternConstructor conName codomainDataVar domainDataVar expectedCodomain sig' decomposes inferred constructor type ('sig')
-- in accordance with the expected data type ('expectedCodomain') type.
-- The decomposed constructor has 'codomainDataVar' as the size variable of its domain
-- and 'domainDataVar' as the size variables of its recursive domains.
freshenPatternConstructor :: QName -> Int -> PatternEncoder Int -> SizeTele -> SizeSignature -> PatternEncoder SizeTele
freshenPatternConstructor conName codomainDataVar domainDataVar expectedCodomain (SizeSignature bounds contra constructorType) = do
  let (SizeTree topSize datatypeParameters) = expectedCodomain
  let shouldBeUnbounded b = b == SizeUnbounded || codomainDataVar == (-1)
  -- We need to strip the codomain size from the constructor here.
  let modifier = if codomainDataVar /= -1 then init else id
  newVarsRaw <- lift $ requestNewRigidVariables topSize (modifier (filter shouldBeUnbounded bounds)) -- tail for stripping codomain TODO
  -- It is important to call `domainDataVar` lazily,
  -- because otherwise leaf variables would gain access to a cluster var with lower level than expected
  domainVar <- if length newVarsRaw + 1 == length bounds then pure (-1) else domainDataVar
  let newVars = snd $ List.mapAccumL (\nv bound -> if shouldBeUnbounded bound then (tail nv, head nv) else (nv, domainVar)) newVarsRaw (modifier bounds)
  reportSDoc "term.tbt" 20 $ vcat
    [ "new vars raw: " <+> text (show newVarsRaw)
    , "bounds: " <+> text (show bounds)
    , "size tele: " <+> text (show constructorType)
    ]
  reportSDoc "term.tbt" 20 $ "new vars: " <+> text (show newVars)
  let instantiatedSig = instantiateSizeTele constructorType (newVars ++ [codomainDataVar])
  freshSig <- lift $ freshenGenericArguments instantiatedSig
  numberOfArguments <- liftTCM $ getDatatypeParametersByConstructor conName
  let partialConstructorType = applyDataType (take numberOfArguments datatypeParameters) freshSig
  return partialConstructorType

freshenCopatternProjection :: Int -> [SizeBound] -> SizeTele -> PatternEncoder SizeTele
freshenCopatternProjection newCoDepthVar bounds tele = do
  let isNewPatternSizeVar b = b == SizeUnbounded || newCoDepthVar == (-1)
  newVarsRaw <- lift $ requestNewRigidVariables SUndefined (filter isNewPatternSizeVar bounds)
  let newVars = snd $ List.mapAccumL (\nv bound -> if isNewPatternSizeVar bound then (tail nv, head nv) else (nv, newCoDepthVar)) newVarsRaw bounds
  reportSDoc "term.tbt" 20 $ "Before instantiation in freshenCopatternConstructor: " <+> text (show tele) <+> "with new vars:" <+> text (show newVars)
  let instantiatedSig = instantiateSizeTele tele newVars
  lift $ freshenGenericArguments instantiatedSig

-- This is a protection against postulated univalence.
-- Normally, there cannot be any relation between a size variable and a generic,
-- but introducing univalence there can actually be a relation between them.
ensurePatternIntegrity :: [SizeTele] -> [SizeTele] -> MonadSizeChecker ()
ensurePatternIntegrity realTypes expectedTypes = do
  let integrityViolation = any (\(realType, expectedType) -> (isGenericVar expectedType) /= (isGenericVar realType)) (zip realTypes expectedTypes)
  when integrityViolation $ MSC $ modify (\s -> s { scsErrorMessages = scsErrorMessages s ++ ["Integrity violation in clause"] })
  where
    isGenericVar :: SizeTele -> Bool
    isGenericVar (SizeGenericVar _ _) = True
    isGenericVar _ = False

-- Extracts cluster of the top-level size expr
getClusterByTele :: SizeTele -> MonadSizeChecker Int
getClusterByTele (SizeTree (SDefined i) _) = do
  ctx <- getCurrentRigids
  pure $ getCluster ctx i
getClusterByTele (SizeArrow _ r) = getClusterByTele r
getClusterByTele (SizeGeneric _ _ r) = getClusterByTele r
getClusterByTele _ = pure (-1)

-- for a pattern size variable, gets its cluster index
getCluster :: [(Int, SizeBound)] -> Int -> Int
getCluster bounds i = case List.lookup i bounds of
  Nothing -> -1
  Just SizeUnbounded -> i
  Just (SizeBounded j) -> getCluster bounds j
