-- ASR (01 June 2014): Not used yet.

-- {-# LANGUAGE NoMonomorphismRestriction #-}
-- {-# LANGUAGE ScopedTypeVariables #-}
-- {-# LANGUAGE TupleSections #-}

-- module Agda.TypeChecking.SizedTypes.Main where

-- import Control.Monad

-- import Data.Functor
-- import Data.Char (isSpace)
-- import qualified Data.Map as Map
-- import qualified Data.Set as Set

-- import System.Exit

-- import Agda.TypeChecking.SizedTypes.Syntax
-- import Agda.TypeChecking.SizedTypes.Parser
-- import Agda.TypeChecking.SizedTypes.WarshallSolver

-- main :: IO ()
-- main = do
--   putStrLn "Size constraint solver (C) 2013 Andreas Abel and Felix Reihl"
--   (hs, pols, cs) <- parseFile . filter (not . all isSpace) . lines <$> getContents

--   unless (null hs) $ do
--     putStrLn "Hypotheses"
--     mapM_ print hs
--   unless (Set.null $ flexs hs) $
--     abort "flexible variables are not allowed in hypotheses"

--   putStrLn "Constraints"
--   mapM_ print cs

--   unless (Map.null pols) $ do
--     putStrLn "Solutions"
--     mapM_ (\ (x,p) -> print $ PolarityAssignment p x) $ Map.toAscList pols

--   hg <- abortOnNothing "invalid hypotheses" $ hypGraph (rigids cs) hs
--   putStrLn $ "Hypotheses graph hg = " ++ show (graphToList hg)
--   -- Test:
--   -- print $ lub' hg (NodeZero, 0) (NodeRigid "i", 0)

--   (xs, gs) <- abortOnNothing "inconsistent constraints" $ constraintGraphs cs hg

--   let xsSol = Map.fromList $ map (,Infty) xs
--   sol <- (Map.union xsSol) <$> do abortOnError $ solveGraphs pols hg gs
--   putStrLn "Solution"
--   print sol

--   abortOnError $ verifySolution hg cs sol

-- abort :: String -> IO a
-- abort msg = do
--   putStrLn $ "Error: " ++ msg
--   exitFailure

-- abortOnError :: Either String a -> IO a
-- abortOnError = either abort return

-- abortOnNothing :: String -> Maybe a -> IO a
-- abortOnNothing msg = maybe (abort msg) return

-- type Constraints = [Constraint]
-- type Hypotheses  = Constraints

-- parseFile :: [String] -> (Hypotheses, Polarities Flex, Constraints)
-- parseFile input = ( map parse hyps
--                   , polaritiesFromAssignments $ map parse pols
--                   , map parse cons
--                   )
--   where
--     (ls1, ls2)   = break isSeparator input
--     (hyps, rest) = if null ls2 then ([], ls1) else (ls1, tail ls2)
--     (ls1', ls2') = break isSeparator rest
--     (pols, cons) = if null ls2' then ([], ls1') else (ls1', tail ls2')


-- -- | A separator is a line consisting entirely of dashes,
-- --   and at least 2 of them.  It may be followed by white space.
-- isSeparator :: String -> Bool
-- isSeparator s = length dashes >= 2 && all isSpace rest
--   where (dashes, rest) = span (== '-') s
