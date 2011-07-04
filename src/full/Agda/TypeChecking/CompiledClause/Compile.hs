module Agda.TypeChecking.CompiledClause.Compile where

import Data.Monoid

import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.TypeChecking.CompiledClause
import Agda.TypeChecking.Monad
import Agda.TypeChecking.RecordPatterns
import Agda.Utils.List

import Agda.Utils.Impossible
#include "../../undefined.h"

compileClauses
  :: MonadTCM tcm
  => Bool
     -- ^ Translate record patterns?
  -> [Clause]
  -> tcm CompiledClauses
compileClauses translate cs = do
  cs <- if translate then
          mapM translateRecordPatterns cs
         else
          return cs
  return $ compile [(clausePats c, clauseBody c) | c <- cs]

type Cl  = ([Arg Pattern], ClauseBody)
type Cls = [Cl]

compile :: Cls -> CompiledClauses
compile cs = case nextSplit cs of
  Just n  -> Case n $ fmap compile $ splitOn n cs
  Nothing -> case map getBody cs of
    [Just (m, t)] -> Done m t
    [Nothing]     -> Fail
    _             -> __IMPOSSIBLE__
  where
    getBody (_, b) = body b
    body (Bind b)   = inc $ body (absBody b)
    body (NoBind b) = body b
    body (Body t)   = Just (0, t)
    body NoBody     = Nothing
    inc Nothing       = Nothing
    inc (Just (n, t)) = Just (n + 1, t)

nextSplit :: Cls -> Maybe Int
nextSplit [] = __IMPOSSIBLE__
nextSplit ((ps, _):_) = mhead [ n | (a, n) <- zip ps [0..], isPat (unArg a) ]
  where
    isPat VarP{} = False
    isPat DotP{} = False
    isPat ConP{} = True
    isPat LitP{} = True

splitOn :: Int -> Cls -> Case Cls
splitOn n cs = mconcat $ map (fmap (:[]) . splitC n) cs

splitC :: Int -> Cl -> Case Cl
splitC n (ps, b) = case unArg p of
  ConP c _ qs -> conCase c (ps0 ++ qs ++ ps1, b)
  LitP l      -> litCase l (ps0 ++ ps1, b)
  _           -> catchAll (ps, b)
  where
    (ps0, p, ps1) = extractNthElement' n ps
