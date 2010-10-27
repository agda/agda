{-# LANGUAGE TypeOperators, CPP, DeriveDataTypeable #-}
module Agda.TypeChecking.CompiledClause where

import qualified Data.Map as Map
import Data.Map (Map)
import Data.Monoid
import Data.Generics

import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.Syntax.Literal
import Agda.Utils.List
import Agda.Utils.Pretty

import Agda.Utils.Impossible
#include "../undefined.h"

type key :-> value = Map key value

data Case c = Branches { conBranches    :: QName   :-> c
                       , litBranches    :: Literal :-> c
                       , catchAllBranch :: Maybe c
                       }
  deriving (Typeable, Data)

data CompiledClauses
  = Case Int (Case CompiledClauses)
  | Done Int Term
  | Fail
  deriving (Typeable, Data)

-- | Note that it is the /translated/ clauses which are compiled, not
-- the original ones.

compileClauses :: [Clauses] -> CompiledClauses
compileClauses cs =
  compile [ (clausePats c, clauseBody c)
          | Clauses { translatedClause = c } <- cs
          ]

type Cl  = ([Arg Pattern], ClauseBody)
type Cls = [Cl]

compile :: Cls -> CompiledClauses
compile cs = case nextSplit cs of
  Just n  -> Case n $ fmap compile $ splitOn n cs
  Nothing -> case map getBody cs of
    [Just (m, t)] -> Done m t
    _             -> Fail
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

litCase l x = Branches Map.empty (Map.singleton l x) Nothing
conCase c x = Branches (Map.singleton c x) Map.empty Nothing
catchAll x  = Branches Map.empty Map.empty (Just x)

instance Functor Case where
  fmap f (Branches cs ls m) = Branches (fmap f cs) (fmap f ls) (fmap f m)

instance Monoid m => Monoid (Case m) where
  mempty = Branches Map.empty Map.empty Nothing
  mappend (Branches cs  ls  m)
          (Branches cs' ls' m') =
    Branches (Map.unionWith mappend cs cs')
             (Map.unionWith mappend ls ls')
             (mappend m m')

instance Pretty a => Show (Case a) where
  show = show . pretty
instance Show CompiledClauses where
  show = show . pretty

instance Pretty a => Pretty (Case a) where
  prettyPrec p (Branches cs ls m) =
    mparens (p > 0) $ vcat $
      pr cs ++ pr ls ++ prC m
    where
      prC Nothing = []
      prC (Just x) = [text "_ ->" <+> pretty x]
      pr m = [ sep [ text (show x ++ " ->")
                   , nest 2 $ pretty v ]
             | (x, v) <- Map.toList m ]

instance Pretty CompiledClauses where
  pretty (Done m t)  = text ("done[" ++ show m ++ "]") <+> text (show t)
  pretty Fail        = text "fail"
  pretty (Case n bs) =
    sep [ text ("case " ++ show n ++ " of")
        , nest 2 $ pretty bs
        ]
