{-# LANGUAGE CPP #-}
module Agda.TypeChecking.DeadCode (eliminateDeadCode) where

import Control.Applicative
import Control.Monad
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Foldable (foldMap, Foldable)
import Data.Traversable (traverse)

import Agda.Syntax.Common
import Agda.Syntax.Literal
import qualified Agda.Syntax.Concrete as C
import qualified Agda.Syntax.Abstract as A

import Agda.Syntax.Internal hiding (Arg, Dom)
import Agda.Syntax.Scope.Base
import Agda.Syntax.Scope.Monad

import qualified Agda.Benchmarking as Bench
import qualified Agda.TypeChecking.Monad.Benchmark as Bench

import Agda.TypeChecking.Monad
import Agda.TypeChecking.CompiledClause
import Agda.TypeChecking.Reduce

import Agda.Utils.HashMap (HashMap)
import qualified Agda.Utils.HashMap as HMap

import Agda.Utils.Impossible
#include "undefined.h"

-- | Run before serialisation to remove any definitions that are not reachable
--   from the public interface to the module.
eliminateDeadCode :: Signature -> TCM Signature
eliminateDeadCode sig = Bench.billTo [Bench.DeadCode] $ do
  patsyn <- getPatternSyns
  public <- Set.map anameName . publicNames <$> getScope
  defs <- traverse instantiateFull $ sigDefinitions sig
  let r     = reachableFrom public patsyn defs
      defs' = HMap.filterWithKey (\ x _ -> Set.member x r) defs
  reportSLn "tc.dead" 10 $ "Removed " ++ show (HMap.size defs - HMap.size defs') ++ " unused definitions."
  return sig{ sigDefinitions = defs' }

reachableFrom :: Set QName -> A.PatternSynDefns -> Definitions -> Set QName
reachableFrom names psyns defs = follow names (Set.toList names)
  where
    follow visited [] = visited
    follow visited (x : xs) = follow (Set.union visited new) (Set.toList new ++ xs)
      where
        new = Set.filter (not . (`Set.member` visited)) $
                case HMap.lookup x defs of
                  Nothing -> namesIn (PSyn <$> Map.lookup x psyns)
                  Just d  -> namesIn d

class NamesIn a where
  namesIn :: a -> Set QName

namesInFoldable :: (Foldable f, NamesIn a) => f a -> Set QName
namesInFoldable x = Set.unions $ foldMap ((:[]) . namesIn) x

instance NamesIn a => NamesIn (Maybe a)       where namesIn = namesInFoldable
instance NamesIn a => NamesIn [a]             where namesIn = namesInFoldable
instance NamesIn a => NamesIn (Arg c a)       where namesIn = namesInFoldable
instance NamesIn a => NamesIn (Dom c a)       where namesIn = namesInFoldable
instance NamesIn a => NamesIn (Named n a)     where namesIn = namesInFoldable
instance NamesIn a => NamesIn (Abs a)         where namesIn = namesInFoldable
instance NamesIn a => NamesIn (WithArity a)   where namesIn = namesInFoldable
instance NamesIn a => NamesIn (Tele a)        where namesIn = namesInFoldable
instance NamesIn a => NamesIn (ClauseBodyF a) where namesIn = namesInFoldable

instance NamesIn a => NamesIn (C.FieldAssignment' a) where namesIn = namesInFoldable

instance (NamesIn a, NamesIn b) => NamesIn (a, b) where
  namesIn (x, y) = Set.union (namesIn x) (namesIn y)

instance (NamesIn a, NamesIn b, NamesIn c) => NamesIn (a, b, c) where
  namesIn (x, y, z) = namesIn (x, (y, z))

instance NamesIn Definition where
  namesIn def = namesIn (defType def, theDef def)

instance NamesIn Defn where
  namesIn def = case def of
    Axiom -> Set.empty
    Function    { funClauses = cl, funCompiled = cc }              -> namesIn (cl, cc)
    Datatype    { dataClause = cl, dataCons = cs, dataSort = s }   -> namesIn (cl, cs, s)
    Record      { recClause = cl, recConHead = c, recFields = fs } -> namesIn (cl, c, fs)
      -- Don't need recTel or recConType since those will be reachable from the constructor
    Constructor { conSrcCon = c, conData = d }                     -> namesIn (c, d)
    Primitive   { primClauses = cl, primCompiled = cc }            -> namesIn (cl, cc)

instance NamesIn Clause where
  namesIn Clause{ clauseTel = tel, namedClausePats = ps, clauseBody = b, clauseType = t } =
    namesIn ((tel, ps, b), t)

instance NamesIn CompiledClauses where
  namesIn (Case _ c) = namesIn c
  namesIn (Done _ v) = namesIn v
  namesIn Fail       = Set.empty

instance NamesIn a => NamesIn (Case a) where
  namesIn Branches{ conBranches = bs, catchAllBranch = c } =
    namesIn (Map.toList bs, c)

instance NamesIn (Pattern' a) where
  namesIn p = case p of
    VarP{}        -> Set.empty
    LitP l        -> namesIn l
    DotP v        -> namesIn v
    ConP c _ args -> namesIn (c, args)
    ProjP f       -> namesIn f

instance NamesIn a => NamesIn (Type' a) where
  namesIn (El s t) = namesIn (s, t)

instance NamesIn Sort where
  namesIn s = case s of
    Type l   -> namesIn l
    Prop     -> Set.empty
    Inf      -> Set.empty
    SizeUniv -> Set.empty
    DLub a b -> namesIn (a, b)

instance NamesIn Term where
  namesIn v = case ignoreSharing v of
    Var _ args   -> namesIn args
    Lam _ b      -> namesIn b
    Lit l        -> namesIn l
    Def f args   -> namesIn (f, args)
    Con c args   -> namesIn (c, args)
    Pi a b       -> namesIn (a, b)
    Sort s       -> namesIn s
    Level l      -> namesIn l
    MetaV _ args -> namesIn args
    DontCare v   -> namesIn v
    Shared{}     -> __IMPOSSIBLE__

instance NamesIn Level where
  namesIn (Max ls) = namesIn ls

instance NamesIn PlusLevel where
  namesIn ClosedLevel{} = Set.empty
  namesIn (Plus _ l)    = namesIn l

instance NamesIn LevelAtom where
  namesIn l = case l of
    MetaLevel _ args -> namesIn args
    BlockedLevel _ v -> namesIn v
    NeutralLevel _ v -> namesIn v
    UnreducedLevel v -> namesIn v

-- For QName literals!
instance NamesIn Literal where
  namesIn l = case l of
    LitInt{}      -> Set.empty
    LitString{}   -> Set.empty
    LitChar{}     -> Set.empty
    LitFloat{}    -> Set.empty
    LitQName _  x -> namesIn x

instance NamesIn a => NamesIn (Elim' a) where
  namesIn (Apply arg) = namesIn arg
  namesIn (Proj f)    = namesIn f

instance NamesIn QName   where namesIn x = Set.singleton x
instance NamesIn ConHead where namesIn h = namesIn (conName h)

-- Pattern synonym stuff --

newtype PSyn = PSyn A.PatternSynDefn
instance NamesIn PSyn where
  namesIn (PSyn (_args, p)) = namesIn p

instance NamesIn (A.Pattern' a) where
  namesIn p = case p of
    A.VarP{}               -> Set.empty
    A.ConP _ c args        -> namesIn (c, args)
    A.DefP _ f args        -> namesIn (f, args)
    A.WildP{}              -> Set.empty
    A.AsP _ _ p            -> namesIn p
    A.AbsurdP{}            -> Set.empty
    A.LitP l               -> namesIn l
    A.PatternSynP _ c args -> namesIn (c, args)
    A.RecP _ fs            -> namesIn fs
    A.DotP{}               -> __IMPOSSIBLE__    -- Dot patterns are not allowed in pattern synonyms

instance NamesIn AmbiguousQName where
  namesIn (AmbQ cs) = namesIn cs

