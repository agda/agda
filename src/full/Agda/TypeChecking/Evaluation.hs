
{-# LANGUAGE Strict #-}

module Agda.TypeChecking.Evaluation where

import Agda.Syntax.Common
import Agda.Syntax.Literal
import qualified Agda.Syntax.Abstract.Name as A
import qualified Agda.Syntax.Internal as I


-- | De Bruijn level.
newtype Lvl = Lvl Int


data PiInfo = PiInfo
data LamInfo = LamInfo
data ConInfo = ConInfo
data ProjInfo = ProjInfo ProjOrigin A.QName
data Closure = Closure Env I.Term

data Spine
  = SId
  | SProj Spine ProjInfo Lvl
  | SApp Spine ArgInfo

data RigidHead
  = RHVar Lvl
  | RHPostulate A.QName

data FlexHead = FHMeta MetaId

data Env
  = ENil
  | EBind Env ~Val

data Sort
  = SetS Val
  | LitS Integer
  | PropS Val
  | PropLitS Integer
  | InfS Integer
  | UnknownS

data Level     = Max Integer [PlusLevel]
data PlusLevel = Plus Integer Val

data Val
  = Rigid RigidHead Spine
  | Flex MetaId Spine
  | Unfold A.QName Spine ~Val
  | Con ConInfo Spine
  | Lit Literal
  | Pi PiInfo ~Val {-# UNPACK #-} Closure
  | Lam LamInfo {-# UNPACK #-} Closure
  | Sort Sort
  | Level {-# UNPACK #-} Level

class Eval a b | a -> b where
  eval :: Env -> a -> b

{-
Plan:
- Ignore cubical
- Ignore rewrite rules
- Forcing should kill solved metas
- We preserve definition unfolding

- Forcing:
  - whnf: unfold solved metas and definitions
  - force: only unfold solved metas

- instantiateFull:
  - We evaluate normally, forcing kills solved metas
  - Readback returns sets of freevars, we use freevars to eta-reduce lambdas
  - eta-reducing records is done the same way as now, by dumb syntactic comparison


Questions:
- In Term, ArgInfo may contain free var sets, when are they actually computed and stored?
- What is LitMeta, how is it different from MetaV in Term?
- What is AllowedReductions?
- Opaque/abstract?



-}
{-
General comments on Reduce:
- interval application is kind of an afterthought on the result of reducion
- builtin nat gets converted to Integer literals (should cache builtin lookup)


Meta instantiation:


Defn unfolding:

sources:
  - stSignature . sigDefinitions
  - stImports   . sigDefinitions


Meta lookup:
 1. lookup from stSolvedMetaStore
 2. lookup from stOpenMetaStore
 3. lookup from stPreImportedMetaStore









Optimization on existing stuff:

- unfoldDefinitionStep (routine list-killing)

- quadratic instantiateFull in "rewrite"
    - remove instantiateFull on the elims
    - it seems that we don't need eta-reduction for matching (we're already eagerly eta-long)
    - make sure that we instantiate in nonLinMatch

- isPropM runs in some smelly monad in unfoldDefinitionStep



-}
