{-# LANGUAGE NondecreasingIndentation #-}

-- | Check that a datatype is strictly positive.
module Agda.TypeChecking.Positivity where

import Prelude hiding ( null, (!!) )

import Control.DeepSeq
import Data.Either
import Data.Foldable (toList)
import Data.Foldable qualified as Fold
import Data.Function (on)
import Data.Graph (SCC(..))
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Sequence (Seq)
import Data.Sequence qualified as DS
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Strict.These

import Agda.Syntax.Common
import Agda.Syntax.Info qualified as Info
import Agda.Syntax.Internal
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Monad.Benchmark (MonadBench, Phase)
import Agda.TypeChecking.Monad.Benchmark qualified as Bench
import Agda.TypeChecking.Positivity.Occurrence
import Agda.TypeChecking.Positivity.OccurrenceAnalysis
import Agda.TypeChecking.Positivity.Warnings qualified as W
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Records
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Warnings

import Agda.Syntax.Common.Pretty (prettyShow)
import Agda.Syntax.Common.Pretty qualified as P
import Agda.Utils.Functor
import Agda.Utils.Graph.AdjacencyMap.Unidirectional qualified as Graph
import Agda.Utils.List
import Agda.Utils.List1 qualified as List1
import Agda.Utils.Maybe
import Agda.Utils.Monad
import Agda.Utils.Null
import Agda.Utils.Size

import Agda.Utils.Impossible

----------------------------------------------------------------------------------------------------

-- | Check that the datatypes in the mutual block containing the given
--   declarations are strictly positive.
--
--   Find polarity of datatypes parameters and indices.
--
--   Also add information about positivity and recursivity of records
--   to the signature.
checkStrictlyPositive :: Info.MutualInfo -> Set QName -> TCM ()
checkStrictlyPositive mi qset = Bench.billTo [Bench.Positivity] do

  let qs = Set.toList qset
  reportSDoc "tc.pos.tick" 100 $ "positivity of" <+> prettyTCM qs

  -- Collect relevant information about the block.
  preprocessBlock qs >>= \case
    Nothing -> do
      pure () -- skip the whole thing if there's nothing to check
    Just blockInfo -> do

      -- compute the occurrence graph
      --------------------------------------------------------------------------------
      (g, mutuals) <- buildOccurrenceGraph qs
      sccs <- lift $ stronglyConnComp g

      -- /lazily computed/ generic graph for debug printing and warnings
      let ggeneric = toGenericGraph g

      reportSDoc "tc.pos.tick" 100 $ "constructed graph"
      reportSLn "tc.pos.graph" 5 $ "Positivity graph: N=" ++ show (size $ Graph.nodes ggeneric) ++
                                   " E=" ++ show (length $ Graph.edges ggeneric)
      reportSDoc "tc.pos.graph" 10 $ vcat
        [ "positivity graph for" <+> fsep (map prettyTCM qs)
        , nest 2 $ prettyTCM ggeneric
        ]

      -- set mutual blocks
      --------------------------------------------------------------------------------
      reportSDoc "tc.pos.graph.sccs" 10 $ do
        let (triv, others) = partitionEithers $ for sccs $ \case
              AcyclicSCC v -> Left v
              CyclicSCC vs -> Right vs
        sep [ text $ show (length triv) ++ " trivial sccs"
            , text $ show (length others) ++ " non-trivial sccs with lengths " ++
                show (map length others)
            ]
      reportSLn "tc.pos.graph.sccs" 15 $
        "  sccs = " ++ prettyShow [ scc | CyclicSCC scc <- sccs ]

      -- #7133: Note that the graph doesn't necessarily contain all of qs in the case where there are no
      -- occurrences of a name, but we still need to setMutual for them.
      let ~sccMap = Map.unions [ case scc of
                                   AcyclicSCC (DefNode q) -> Map.singleton q []
                                   AcyclicSCC ArgNode{}   -> mempty
                                   CyclicSCC scc          -> Map.fromList [ (q, qs) | q <- qs ]
                                     where qs = [ q | DefNode q <- scc ]
                               | scc <- sccs ]

      inAbstractMode $ forM_ qs \q -> do
        whenM (isNothing <$> getMutual q) do

          let qs = fromMaybe [] $ Map.lookup q sccMap
          reportSLn "tc.pos.mutual" 10 $ "setting " ++ prettyShow q ++ " to " ++
                                         if | null qs        -> "non-recursive"
                                            | length qs == 1 -> "recursive"
                                            | otherwise      -> "mutually recursive"
          setMutual q qs

      forM_ blockInfo \(q, arity, dataTypeOrRec, _) -> inConcreteOrAbstractMode q \_ -> do

        -- set argument occurrences
        --------------------------------------------------------------------------------
        when (arity > 0) do
          reportSDoc "tc.pos.args" 10 $ "computing arg occurrences of " <+> prettyTCM q

          -- If there is no outgoing edge @ArgNode q i@, all @n@ arguments are @Unused@.
          -- Otherwise, we obtain the occurrences from the Graph.
          !args <- forM [0 .. arity-1] \i -> lift $ transitiveOccurrence g (ArgNode q i) (DefNode q)
              --   [0 .. max m (arity - 1)] -- triggers issue #3049

          reportSDoc "tc.pos.args" 10 $ sep
            [ "args of" <+> prettyTCM q <+> "="
            , nest 2 $ prettyList $ map prettyTCM args
            ]

          let mergeOccs :: [Occurrence] -> [Occurrence] -> [Occurrence]
              mergeOccs poccs toccs =
                -- Lucas, 2022-12-01:
                -- `poccs` are the occurences computed by the positivity-checker
                -- `toccs` are the occurences/polarities explicitely given by the user
                --   (and enforced through type-checking)
                -- We consider the polarities explicitely given (toccs) to take priority over the ones
                -- found out by the positivity checker.
                -- Note: Alas, this is hard to enforce given that non-annotated variables are
                -- always annotated with Mixed polarity. If the annotated polarity is Mixed,
                -- for now we always rely on the result from the positivity analysis.
                align poccs toccs <&> mergeThese (\a b -> if b == Mixed then a else b)

          !oldOccs <- getArgOccurrences q
          let !newOccs = let x = mergeOccs args oldOccs in deepseq x x
          setArgOccurrences q newOccs
          reportSDoc "tc.pos.tick" 100 $ "set args"


        -- check positivity
        --------------------------------------------------------------------------------
        case dataTypeOrRec of
          Nothing -> pure ()
          Just (pc, dr) -> do
            reportSDoc "tc.pos.check" 10 $ "Checking positivity of" <+> prettyTCM q

            let ~ggeneric' = fmap (fmap DS.singleton) ggeneric

                reason bound =
                  case W.productOfEdgesInBoundedWalk
                         (\(Edge o _) -> o) ggeneric' (DefNode q) (DefNode q) bound of
                    Just (Edge _ how) -> how
                    Nothing           -> __IMPOSSIBLE__

                how :: String -> Occurrence -> TCM Doc
                how msg bound = fsep $
                      [prettyTCM q] ++ pwords "is" ++
                      pwords (msg ++ ", because it occurs") ++
                      [prettyTCM (reason bound)]

            -- if we have a negative loop, raise error
            -- ASR (23 December 2015). We don't raise a strictly positive
            -- error if the NO_POSITIVITY_CHECK pragma was set. See Issue 1614.
            -- Andreas, 2026-02-27:
            -- This information now comes either with the mututal block
            -- or with the data/record type, see issue #3355.
            loop <- do
              posCheck <- positivityCheckEnabled
              let nopc = NoPositivityCheck
              if Info.mutualPositivityCheck mi == nopc || pc == nopc || not posCheck then
                pure Nothing
              else do
                loop <- lift $ transitiveOccurrence g (DefNode q) (DefNode q)
                when (loop <= JustPos) $ warning $ NotStrictlyPositive q (reason JustPos)
                pure $ Just loop

            let checkInduction :: QName -> TCM ()
                checkInduction q =
                  -- Check whether the recursive record has been declared as
                  -- 'Inductive' or 'Coinductive'.  Otherwise, error.
                  unlessM (isJust . recInduction . theDef <$> getConstInfo q) $
                    setCurrentRange (nameBindingSite q) $
                      warning $ RecursiveRecordNeedsInductivity q

            -- Recursivity needs to be declared for inductive records.
            -- Eta should be off for unguarded records.
            case dr of
              IsData -> return ()
              IsRecord pat -> do
                loop <- case loop of
                  Nothing   -> lift $ transitiveOccurrence g (DefNode q) (DefNode q)
                  Just loop -> pure loop
                case loop of
                  o | o <= StrictPos -> do
                    reportSDoc "tc.pos.record" 5 $ how "not guarded" StrictPos
                    unguardedRecord q
                    checkInduction q
                  o | o <= GuardPos -> do
                    reportSDoc "tc.pos.record" 5 $ how "recursive" GuardPos
                    checkInduction q
                  Unused -> reportSDoc "tc.pos.record" 10 $
                    "record type" <+> prettyTCM q <+> "is not recursive"
                  _ -> return ()

  reportSDoc "tc.pos.tick" 100 $ "checked positivity"

getDefArity :: Definition -> TCM Int
getDefArity def = do
  let go :: Type -> Int -> ReduceM Int
      go !a !n = (unEl <$> reduce a) >>= \case
        Pi a b -> underAbsReduceM a b \b -> go b (n + 1)
        _      -> pure n
  n <- liftReduce (go (defType def) 0)
  pure $! n - projectionArgs def

-- Andreas, 2018-11-23, issue #3404
-- Only assign argument occurrences to things which have a definition.
-- Things without a definition would be judged "constant" in all arguments,
-- since no occurrence could possibly be found, naturally.
hasDefinition :: Defn -> Bool
hasDefinition = \case
  Axiom{}            -> False
  DataOrRecSig{}     -> False
  GeneralizableVar{} -> False
  AbstractDefn{}     -> False
  Primitive{}        -> False
  PrimitiveSort{}    -> False
  Constructor{}      -> False
  Function{}         -> True
  Datatype{}         -> True
  Record{}           -> True

isDatatype :: Definition -> Maybe (PositivityCheck, DataOrRecord)
isDatatype def = do
  case theDef def of
    Datatype{dataClause = Nothing, dataPositivityCheck} ->
      Just (dataPositivityCheck, IsData)
    Record  {recClause  = Nothing, recPositivityCheck, recPatternMatching } ->
      Just (recPositivityCheck, IsRecord recPatternMatching)
    _ -> Nothing

-- Result: [(name, arity, data or record, do we need to setMutual)] or Nothing if we don't need any
-- occurrence analysis.
preprocessBlock :: [QName] -> TCM (Maybe ([(QName, Int, Maybe (PositivityCheck, DataOrRecord), Bool)]))
preprocessBlock qs = do
  let go []     = pure []
      go (q:qs) = inConcreteOrAbstractMode q \def -> do
        !arity <- case hasDefinition (theDef def) of
          True  -> getDefArity def
          False -> pure 0
        let !dr = isDatatype def
        let !needToSetMutual = isNothing (getMutual_ (theDef def))
        !rest <- go qs
        pure ((q, arity, dr, needToSetMutual) : rest)
  info <- go qs
  case any (\(_, arity, dr, setMut) -> arity /= 0 || isJust dr || setMut) info of
    True -> pure $ Just info
    _    -> pure Nothing


-- Pretty printing
----------------------------------------------------------------------------------------------------

instance PrettyTCM Node where
  prettyTCM = return . P.pretty

instance P.Pretty a => PrettyTCMWithNode (Edge a) where
  prettyTCMWithNode (WithNode n (Edge o w)) = vcat
    [ prettyTCM o <+> prettyTCM n
    , nest 2 $ return $ P.pretty w
    ]

instance PrettyTCM (Seq W.OccursWhere) where
  prettyTCM =
    fmap snd . prettyOWs . map adjustLeftOfArrow . uniq . Fold.toList
    where
      nth 0 = pwords "first"
      nth 1 = pwords "second"
      nth 2 = pwords "third"
      nth n = pwords $ show (n + 1) ++ "th"

      -- Removes consecutive duplicates.
      uniq :: [W.OccursWhere] -> [W.OccursWhere]
      uniq = map List1.head . List1.groupBy ((==) `on` snd')
        where
        snd' (W.OccursWhere _ _ ws) = ws

      prettyOWs :: MonadPretty m => [W.OccursWhere] -> m (String, Doc)
      prettyOWs []  = __IMPOSSIBLE__
      prettyOWs [o] = do
        (s, d) <- prettyOW o
        return (s, d <> ".")
      prettyOWs (o:os) = do
        (s1, d1) <- prettyOW  o
        (s2, d2) <- prettyOWs os
        return (s1, d1 <> ("," P.<+> "which" P.<+> P.text s2 P.$$ d2))

      prettyOW :: MonadPretty m => W.OccursWhere -> m (String, Doc)
      prettyOW (W.OccursWhere _ cs ws)
        | null cs   = prettyWs ws
        | otherwise = do
            (s, d1) <- prettyWs ws
            (_, d2) <- prettyWs cs
            return (s, d1 P.$$ "(" <> d2 <> ")")

      prettyWs :: MonadPretty m => Seq W.Where -> m (String, Doc)
      prettyWs ws = case Fold.toList ws of
        [W.InDefOf d, W.InIndex] ->
          (,) "is" <$> fsep (pwords "an index of" ++ [prettyTCM d])
        _ ->
          (,) "occurs" <$>
            Fold.foldrM (\w d -> return d $$ fsep (prettyW w)) empty ws

      prettyW :: MonadPretty m => W.Where -> [m Doc]
      prettyW = \case
        W.LeftOfArrow  -> pwords "to the left of an arrow"
        W.DefArg q i   -> pwords "in the" ++ nth i ++ pwords "argument of" ++
                          [prettyTCM q]
        W.UnderInf     -> pwords "under" ++
                           [do -- this cannot fail if an 'UnderInf' has been generated
                            inf <- fromMaybe __IMPOSSIBLE__ <$> getBuiltinName' builtinInf
                            prettyTCM inf]
        W.VarArg p i   -> pwords "in an argument of a bound variable at position" ++ [prettyTCM i]
                         ++ pwords "which uses its argument with polarity" ++ [ pretty p ]
        W.MetaArg      -> pwords "in an argument of a metavariable"
        W.ConArgType c -> pwords "in the type of the constructor" ++ [prettyTCM c]
        W.IndArgType c -> pwords "in an index of the target type of the constructor" ++ [prettyTCM c]
        W.ConEndpoint c -> pwords "in an endpoint of the target of the" ++
                           pwords "higher constructor" ++ [prettyTCM c]
        W.InClause i   -> pwords "in the" ++ nth i ++ pwords "clause"
        W.Matched      -> pwords "as matched against"
        W.InIndex      -> pwords "as an index"
        W.InDefOf d    -> pwords "in the definition of" ++ [prettyTCM d]

      adjustLeftOfArrow :: W.OccursWhere -> W.OccursWhere
      adjustLeftOfArrow (W.OccursWhere r cs os) =
        W.OccursWhere r (DS.filter (not . isArrow) cs) $
          noArrows
            DS.><
          case DS.viewl startsWithArrow of
            DS.EmptyL  -> DS.empty
            w DS.:< ws -> w DS.<| DS.filter (not . isArrow) ws
        where
        (noArrows, startsWithArrow) = DS.breakl isArrow os

        isArrow W.LeftOfArrow{} = True
        isArrow _               = False
