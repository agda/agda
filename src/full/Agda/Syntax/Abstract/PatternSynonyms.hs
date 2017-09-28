
-- | Matching abstract expressions against pattern synonyms for the purpose of
--   printing.
module Agda.Syntax.Abstract.PatternSynonyms
  ( matchPatternSyn
  , matchPatternSynP
  ) where

import Control.Applicative
import Control.Monad.Writer hiding (forM)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Traversable (forM)
import Data.List
import Data.Void

import Agda.Syntax.Common
import Agda.Syntax.Position
import Agda.Syntax.Literal
import Agda.Syntax.Abstract
import Agda.Syntax.Abstract.Views
import Agda.Utils.Monad

-- | Match an expression against a pattern synonym.
matchPatternSyn :: PatternSynDefn -> Expr -> Maybe [Arg Expr]
matchPatternSyn = runMatch match
  where
    match (VarP x) e = x ==> e
    match (LitP l) (Lit l') = guard (l == l')
    match (ConP _ (AmbQ cs) ps) e = do
      Application (Con (AmbQ cs')) args <- return (appView e)
      guard $ null (cs' \\ cs)                          -- check all possible constructors appear in the synonym
      guard $ map getArgInfo ps == map getArgInfo args  -- check that we agree on the hiding (TODO: too strict?)
      zipWithM_ match (map namedArg ps) (map namedArg args)
    match _ _ = empty

-- | Match a pattern against a pattern synonym.
matchPatternSynP :: PatternSynDefn -> Pattern' e -> Maybe [Arg (Pattern' e)]
matchPatternSynP = runMatch match
  where
    match (VarP x) q = x ==> q
    match (LitP l) (LitP l') = guard (l == l')
    match (WildP _) (WildP _) = return ()
    match (ConP _ (AmbQ cs) ps) (ConP _ (AmbQ cs') qs) = do
      guard $ null (cs' \\ cs)
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

