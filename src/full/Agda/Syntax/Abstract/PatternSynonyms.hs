
-- | Pattern synonym utilities: folding pattern synonym definitions for
--   printing and merging pattern synonym definitions to handle overloaded
--   pattern synonyms.
module Agda.Syntax.Abstract.PatternSynonyms
  ( matchPatternSyn
  , matchPatternSynP
  , mergePatternSynDefs
  ) where

import Control.Applicative ( Alternative(empty) )
import Control.Monad.Writer hiding (forM)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Traversable (forM)
import Data.List
import Data.Void

import Agda.Syntax.Common
import Agda.Syntax.Abstract
import Agda.Syntax.Abstract.Views
import Agda.Utils.NonemptyList


-- | Merge a list of pattern synonym definitions. Fails unless all definitions
--   have the same shape (i.e. equal up to renaming of variables and constructor
--   names).
mergePatternSynDefs :: NonemptyList PatternSynDefn -> Maybe PatternSynDefn
mergePatternSynDefs (def :! defs) = foldM mergeDef def defs

mergeDef :: PatternSynDefn -> PatternSynDefn -> Maybe PatternSynDefn
mergeDef (xs, p) (ys, q) = do
  guard $ map getArgInfo xs == map getArgInfo ys
  let ren = zip (map unArg xs) (map unArg ys)
  (xs,) <$> merge ren p q
  where
    merge ren p@(VarP x) (VarP y)   = p <$ guard (elem (unBind x, unBind y) ren)
    merge ren p@(LitP l) (LitP l')  = p <$ guard (l == l')
    merge ren p@(WildP _) (WildP _) = return p
    merge ren (ConP i (AmbQ cs) ps) (ConP _ (AmbQ cs') qs) = do
      guard $ map getArgInfo ps == map getArgInfo qs
      ConP i (AmbQ $ unionNe cs cs') <$> zipWithM (mergeArg ren) ps qs
    merge _ _ _ = empty

    mergeArg ren p q = setNamedArg p <$> merge ren (namedArg p) (namedArg q)

-- | Match an expression against a pattern synonym.
matchPatternSyn :: PatternSynDefn -> Expr -> Maybe [Arg Expr]
matchPatternSyn = runMatch match
  where
    match (VarP x) e = unBind x ==> e
    match (LitP l) (Lit l') = guard (l == l')
    match (ConP _ (AmbQ cs) ps) e = do
      Application (Con (AmbQ cs')) args <- return (appView e)
      guard $ null (toList cs' \\ toList cs)            -- check all possible constructors appear in the synonym
      guard $ map getArgInfo ps == map getArgInfo args  -- check that we agree on the hiding (TODO: too strict?)
      zipWithM_ match (map namedArg ps) (map namedArg args)
    match _ _ = empty

-- | Match a pattern against a pattern synonym.
matchPatternSynP :: PatternSynDefn -> Pattern' e -> Maybe [Arg (Pattern' e)]
matchPatternSynP = runMatch match
  where
    match (VarP x) q = unBind x ==> q
    match (LitP l) (LitP l') = guard (l == l')
    match (WildP _) (WildP _) = return ()
    match (ConP _ (AmbQ cs) ps) (ConP _ (AmbQ cs') qs) = do
      guard $ null (toList cs' \\ toList cs)
      guard $ map getArgInfo ps == map getArgInfo qs
      zipWithM_ match (map namedArg ps) (map namedArg qs)
    match _ _ = empty

type Match e = WriterT (Map Name e) Maybe

(==>) :: Name -> e -> Match e ()
x ==> e = tell (Map.singleton x e)

runMatch :: (Pattern' Void -> e -> Match e ()) -> PatternSynDefn -> e -> Maybe [Arg e]
runMatch match (xs, pat) e = do
  sub <- execWriterT (match pat e)
  forM xs $ \ x -> (<$ x) <$> Map.lookup (unArg x) sub
