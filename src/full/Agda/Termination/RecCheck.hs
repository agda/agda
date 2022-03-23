
{- | Checking for recursion:

   - We detect truly (co)recursive definitions by computing the
     dependency graph and checking for cycles.

   - This is inexpensive and let us skip the termination check
     when there's no (co)recursion

   Original contribution by Andrea Vezzosi (sanzhiyan).
   This implementation by Andreas.
-}


module Agda.Termination.RecCheck
    ( recursive
    , anyDefs
    )
 where

import Control.Monad (forM, forM_)
import Data.Graph
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import qualified Data.Map as Map
import qualified Data.Map.Strict as MapS
import Data.Maybe
import Data.Set (Set)
import qualified Data.Set as Set

import Agda.Syntax.Internal
import Agda.Syntax.Internal.Defs

import Agda.TypeChecking.Monad

import Agda.Utils.List    (hasElem)
import Agda.Utils.Pretty  (prettyShow)

import Agda.Utils.Impossible

-- | We compute for each clause the set of potentially recursive names.
type NamesPerClause = IntMap (Set QName)

-- | Given a list of formally mutually recursive functions,
--   check for actual recursive calls in the bodies of these functions.
--   Returns the actually recursive functions as strongly connected components.
--
--   As a side effect, update the 'clauseRecursive' field in the
--   clauses belonging to the given functions.
recursive :: [QName] -> TCM [[QName]]
recursive names = do
  -- For each function, get names per clause and total.
  (perClauses, nss) <- unzip <$> mapM (recDef (names `hasElem`)) names
  -- Create graph suitable for stronglyConnComp.
  -- Nodes are identical to node keys.
  let graph  = zipWith (\ x ns -> (x, x, Set.toList ns)) names nss
  let sccs   = stronglyConnComp graph
  let nonRec = mapMaybe (\case{ AcyclicSCC x -> Just x ; _ -> Nothing}) sccs
  let recs   = mapMaybe (\case{ CyclicSCC xs -> Just xs; _ -> Nothing}) sccs

  reportSLn "rec.graph" 60 $ show graph

  -- Mark all non-recursive functions and their clauses as such.
  mapM_ markNonRecursive nonRec

  -- Mark individual clauses of recursive functions:
  --------------------------------------------------
  -- Map names to clause numbers to sets of mentioned names.
  let clMap = Map.fromListWith __IMPOSSIBLE__ $ zip names perClauses
  -- Walk through SCCs.
  forM_ recs $ \ scc -> do
    -- Does a set of names have an overlap with the current scc?
    let overlap s = any (`Set.member` s) scc
    -- Walk through members of SCC.
    forM_ scc $ \ x -> do
      -- Get the NamesPerClause for the current function x.
      let perClause  = Map.findWithDefault __IMPOSSIBLE__ x clMap
      -- A clause is recursive if its calls overlap with its scc.
      let recClause i = overlap $ IntMap.findWithDefault __IMPOSSIBLE__ i perClause
      markRecursive recClause x

  -- Return recursive SCCs.
  return recs

-- | Mark a function as terminating and all its clauses as non-recursive.
markNonRecursive :: QName -> TCM ()
markNonRecursive q = modifySignature $ updateDefinition q $ updateTheDef $ \case
  def@Function{} -> def
   { funTerminates = Just True
   , funClauses    = map (\ cl -> cl { clauseRecursive = Just False }) $ funClauses def
   }
  def@Record{} -> def
   { recTerminates = Just True
   }
  def -> def

-- | Mark all clauses of a function as recursive or non-recursive.
markRecursive
  :: (Int -> Bool)  -- ^ Which clauses are recursive?
  -> QName -> TCM ()
markRecursive f q = modifySignature $ updateDefinition q $ updateTheDef $ \case
  def@Function{} -> def
   { funClauses    = zipWith (\ i cl -> cl { clauseRecursive = Just (f i) }) [0..] $ funClauses def
   }
  def -> def

-- | @recDef names name@ returns all definitions from @names@
--   that are used in the type and body of @name@.
recDef :: (QName -> Bool) -> QName -> TCM (NamesPerClause, Set QName)
recDef include name = do
  -- Retrieve definition
  def <- getConstInfo name

  -- Get names in type
  ns1 <- anyDefs include (defType def)

  -- Get names in body
  (perClause, ns2) <- case theDef def of

    Function{ funClauses = cls } -> do
      perClause <- do
        forM (zip [0..] cls) $ \ (i, cl) ->
          (i,) <$> anyDefs include cl
      return (IntMap.fromList perClause, mconcat $ map snd perClause)

    Record{ recTel } -> do
      ns <- anyDefs include recTel
      return (IntMap.singleton 0 ns, ns)

    _ -> return (mempty, mempty)

  reportS "rec.graph" 20
    [ "recDef " ++ prettyShow name
    , "  names in the type: " ++ prettyShow ns1
    , "  names in the def:  " ++ prettyShow ns2
    ]
  return (perClause, ns1 `mappend` ns2)

-- | @anysDef names a@ returns all definitions from @names@
--   that are used in @a@.
anyDefs :: GetDefs a => (QName -> Bool) -> a -> TCM (Set QName)
anyDefs include a = do
  -- Prepare function to lookup metas outside of TCM
  st <- useR stSolvedMetaStore
  let lookup x = inst . mvInstantiation <$> MapS.lookup x st
      -- we collect only those used definitions that are in @names@
      emb d = if include d then Set.singleton d else Set.empty
  -- get all the Defs that are in names
  return $ getDefs' lookup emb a
  where
  -- TODO: Is it bad to ignore the lambdas?
  inst (InstV i)                      = instBody i
  inst Open                           = __IMPOSSIBLE__
  inst OpenInstance                   = __IMPOSSIBLE__
  inst BlockedConst{}                 = __IMPOSSIBLE__
  inst PostponedTypeCheckingProblem{} = __IMPOSSIBLE__
