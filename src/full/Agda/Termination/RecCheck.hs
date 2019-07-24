
{- Checking for recursion:

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

import Data.Graph
import Data.List (nub)
import qualified Data.IntMap as IntMap

import Agda.Syntax.Internal
import Agda.Syntax.Internal.Defs

import Agda.TypeChecking.Monad

import Agda.Utils.Pretty (prettyShow)

recursive :: [QName] -> TCM Bool
recursive names = do
  graph <- zip names <$> mapM (\ d -> nub <$> recDef names d) names
  reportSLn "rec.graph" 20 $ show graph
  return $ cyclic graph

-- | A graph is cyclic if it has any strongly connected component.
cyclic :: [(QName, [QName])] -> Bool
cyclic g = or [ True | CyclicSCC _ <- stronglyConnComp g' ]
  where g' = map (\ (n, ns) -> ((), n, ns)) g

-- | @recDef names name@ returns all definitions from @names@
--   that are used in the type and body of @name@.
recDef :: [QName] -> QName -> TCM [QName]
recDef names name = do
  -- Retrieve definition
  def <- getConstInfo name

  -- Get names in type
  ns1 <- anyDefs names (defType def)

  -- Get names in body
  ns2 <- case theDef def of
    Function{ funClauses = cls } -> anyDefs names cls
    _ -> return []

  reportS "rec.graph" 20
    [ "recDef " ++ prettyShow name
    , "  names in the type: " ++ show ns1
    , "  names in the def:  " ++ show ns2
    ]
  return $ ns1 `mappend` ns2

-- | @anysDef names a@ returns all definitions from @names@
--   that are used in @a@.
anyDefs :: GetDefs a => [QName] -> a -> TCM [QName]
anyDefs names a = do
  -- Prepare function to lookup metas outside of TCM
  st <- getMetaStore
  let lookup (MetaId x) = case mvInstantiation <$> IntMap.lookup x st of
        Just (InstV _ v) -> Just v    -- TODO: ignoring the lambdas might be bad?
        _                -> Nothing
      -- we collect only those used definitions that are in @names@
      emb d = if d `elem` names then [d] else []
  -- get all the Defs that are in names
  return $ getDefs' lookup emb a
