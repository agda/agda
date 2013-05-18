{- Checking for recursion:

   - We detect truly (co)recursive definitions by computing the
     dependency graph and checking for cycles.

   - This is inexpensive and let us skip the termination check
     when there's no (co)recursion

   Original contribution by Andrea Vezzosi (sanzhiyan).
-}

module Agda.Termination.RecCheck
    ( recursive )
 where

import Control.Applicative

import Data.Graph

import Data.List (nub)
import qualified Data.Map as Map
import Data.Map (Map)

import Agda.Syntax.Internal
import Agda.Syntax.Internal.Defs

import Agda.TypeChecking.Monad

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
--   that are used in the body of @name@.
recDef :: [QName] -> QName -> TCM [QName]
recDef names name = do
  -- Retrieve definition
  def <- getConstInfo name
  case theDef def of
    Function{ funClauses = cls } -> do
      -- Prepare function to lookup metas outside of TCM
      st <- getMetaStore
      let lookup x = case mvInstantiation <$> Map.lookup x st of
            Just (InstV v) -> Just v
            _              -> Nothing
      -- get all the Defs that are in names
      return $ getDefs' lookup (`elem` names) cls
    _ -> return []
