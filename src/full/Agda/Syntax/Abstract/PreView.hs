
module Agda.Syntax.Abstract.PreView where

import Prelude hiding (null)

import Control.Applicative ( Const(Const), getConst )
import Control.Monad.Identity
import Control.Monad.State.Strict (State, evalState, get, modify')

import Data.Foldable (foldMap)
import qualified Data.DList as DL
import Data.Void

import Agda.Syntax.Common
import Agda.Syntax.Abstract as A
import Agda.Syntax.Concrete (FieldAssignment', exprFieldA, TacticAttribute')
import Agda.Syntax.Info
import Agda.Syntax.Scope.Base (KindOfName(..), conKindOfName, WithKind(..))
import Agda.Syntax.Position (HasRange, Range'(..), Range, noRange, rangeToPosPair, getRange)

import Agda.Utils.Either
import Agda.Utils.List1 (List1, pattern (:|))
import Agda.Utils.Null
import Agda.Utils.Singleton
import Agda.Utils.Maybe

import Agda.Utils.Impossible

import Agda.Syntax.Abstract.Views
import Control.Monad.Trans.State (StateT(..), runStateT, modify)
-- * Traversal
---------------------------------------------------------------------------

class Monad m => DepthAware m where

  
  wrapLevel :: m a -> m a

-- Instance for StateT Int m
instance Monad m => DepthAware (StateT Int m) where
 wrapLevel ma = do
  modify (+ 1)
  a <- ma
  modify (subtract 1)
  pure a

    
type RecurseLikeFn'   m a = (Monad m  , DepthAware m) =>
  (forall b. ExprLike' b => b -> m b -> m b) -> a -> m a
type TraverseLikeFn'  m a = (Monad m) => (forall b. ExprLike' b => b -> m b) -> a -> m a
type FoldLikeFn'      m a = Monoid m => (forall b. ExprLike' b => b -> m) -> a -> m
type TraverseLikeRecFn' m = forall b. ExprLike' b => b -> m b

-- | Apply an expression rewriting to every subexpression, inside-out.
--   See "Agda.Syntax.Internal.Generic".
class ExprLike a => ExprLike' a where

  recurseExprLike'Raw :: RecurseLikeFn' m a
  default recurseExprLike'Raw
    :: (Traversable t, ExprLike' a', a ~ t a', Monad m , DepthAware m)
    => (forall b. ExprLike' b => b -> m b -> m b) -> a -> m a
  recurseExprLike'Raw g x = ((g x (traverse (recurseExprLike' g) x)))

recurseExprLike' :: ExprLike' a => RecurseLikeFn' m a
recurseExprLike' g x = wrapLevel (recurseExprLike'Raw g x)

traverseExprLike' :: (ExprLike' a , DepthAware m) => TraverseLikeFn' m a
traverseExprLike' g = recurseExprLike' (\_ pre -> pre >>= g)

  
instance ExprLike' Expr where

  recurseExprLike'Raw :: forall m. RecurseLikeFn' m Expr
  recurseExprLike'Raw g e0 = (g e0 $ do
    let rec :: TraverseLikeRecFn' m
        rec = recurseExprLike' g
    case e0 of
      Var{}                      -> pure e0
      Def'{}                     -> pure e0
      Proj{}                     -> pure e0
      Con{}                      -> pure e0
      Lit{}                      -> pure e0
      QuestionMark{}             -> pure e0
      Underscore{}               -> pure e0
      Dot ei e                   -> Dot ei <$> rec e
      App ei e arg               -> App ei <$> rec e <*> rec arg
      WithApp ei e es            -> WithApp ei <$> rec e <*> rec es
      Lam ei b e                 -> Lam ei <$> rec b <*> rec e
      AbsurdLam{}                -> pure e0
      ExtendedLam ei di re x cs  -> ExtendedLam ei di re x <$> rec cs
      Pi ei tel e                -> Pi ei <$> rec tel <*> rec e
      Generalized s e            -> Generalized s <$> rec e
      Fun ei arg e               -> Fun ei <$> rec arg <*> rec e
      Let ei bs e                -> Let ei <$> rec bs <*> rec e
      Rec kwr ei bs              -> Rec kwr ei <$> rec bs
      RecUpdate kwr ei e bs      -> RecUpdate kwr ei <$> rec e <*> rec bs
      RecWhere kwr ei bs e       -> RecWhere kwr ei <$> rec bs <*> rec e
      RecUpdateWhere k r ei e bs -> RecUpdateWhere k r ei <$> rec e <*> rec bs
      ScopedExpr sc e            -> ScopedExpr sc <$> rec e
      Quote{}                    -> pure e0
      QuoteTerm{}                -> pure e0
      Unquote{}                  -> pure e0
      DontCare e                 -> DontCare <$> rec e
      PatternSyn{}               -> pure e0
      Macro{}                    -> pure e0) 

instance ExprLike' a => ExprLike' (Arg a) where
  

instance ExprLike' a => ExprLike' (Maybe a) where
  

instance ExprLike' a => ExprLike' (Named x a) where
  

instance ExprLike' a => ExprLike' (Ranged a) where
  

instance ExprLike' a => ExprLike' [a] where


instance ExprLike' a => ExprLike' (List1 a) where


instance ExprLike' a => ExprLike' (TacticAttribute' a) where

instance (ExprLike' a, ExprLike' b) => ExprLike' (a, b) where

instance ExprLike' Void where
  recurseExprLike'Raw _ = absurd

instance ExprLike' a => ExprLike' (FieldAssignment' a) where

  recurseExprLike'Raw g = exprFieldA (recurseExprLike' g)

instance (ExprLike' a, ExprLike' b) => ExprLike' (Either a b) where

instance ExprLike' BindName where

  recurseExprLike'Raw g x = g x (pure x)
instance ExprLike' ModuleName where

  recurseExprLike'Raw g x = g x (pure x)
instance ExprLike' QName where

  recurseExprLike'Raw g x = g x (pure x)

instance ExprLike' LamBinding where

  recurseExprLike'Raw :: forall m. RecurseLikeFn' m LamBinding
  recurseExprLike'Raw g e =
    g e $ case e of
      DomainFree t x -> DomainFree <$> rec t <*> pure x
      DomainFull bs  -> DomainFull <$> rec bs
    where
      rec :: forall b. ExprLike' b => b -> m b
      rec = recurseExprLike' g

instance ExprLike' GeneralizeTelescope where

  recurseExprLike'Raw g (GeneralizeTel s tel) =
    g (GeneralizeTel s tel) (GeneralizeTel s <$> rec tel)
    where rec = recurseExprLike' g

instance ExprLike' DataDefParams where

  recurseExprLike'Raw g (DataDefParams s tel) =
    g (DataDefParams s tel) (DataDefParams s <$> rec tel)
    where rec = recurseExprLike' g

instance ExprLike' TypedBindingInfo where
  recurseExprLike'Raw g (TypedBindingInfo s t) =
    g (TypedBindingInfo s t) (TypedBindingInfo <$> rec s <*> pure t)
    where rec = recurseExprLike' g

instance ExprLike' TypedBinding where
  recurseExprLike'Raw :: forall m. RecurseLikeFn' m TypedBinding
  recurseExprLike'Raw g tb =
    g tb $ case tb of
      TBind r t xs e' -> TBind r <$> rec t <*> pure xs <*> rec e'
      TLet  r ds      -> TLet  r <$> rec ds
    where
      rec :: forall b. ExprLike' b => b -> m b
      rec = recurseExprLike' g
      
instance ExprLike' LetBinding where
  recurseExprLike'Raw :: forall m. RecurseLikeFn' m LetBinding
  recurseExprLike'Raw g lb = g lb $ case lb of
    LetBind li ai x e e'  -> LetBind li ai x <$> rec e <*> rec e'
    LetAxiom li ai x e    -> LetAxiom li ai x <$> rec e
    LetPatBind li ai p e  -> LetPatBind li ai <$> rec p <*> rec e
    LetApply{}            -> pure lb
    LetOpen{}             -> pure lb
    where rec :: TraverseLikeRecFn' m
          rec = recurseExprLike' g

instance ExprLike' AmbiguousQName where

  -- node-level traversal over the AmbiguousQName and its QNames
  recurseExprLike'Raw :: forall m. RecurseLikeFn' m AmbiguousQName
  recurseExprLike'Raw g aq@(AmbQ qs) =
    g aq (AmbQ <$> rec qs)
    where
      rec :: forall b. ExprLike' b => b -> m b
      rec = recurseExprLike' g
      
instance ExprLike' a => ExprLike' (Pattern' a) where

  recurseExprLike'Raw :: forall m. RecurseLikeFn' m (Pattern' a)
  recurseExprLike'Raw g p =
    g p $ case p of
      VarP x              -> VarP <$> rec x
      ConP i q as         -> ConP i <$> rec q <*> rec as
      ProjP i o q         -> pure (ProjP i o q)
      DefP i q as         -> DefP i <$> rec q <*> rec as
      WildP i             -> pure (WildP i)
      AsP i n p'          -> AsP i <$> rec n <*> rec p'
      DotP i e            -> DotP i <$> rec e
      AbsurdP i           -> pure (AbsurdP i)
      LitP i l            -> pure (LitP i l)
      PatternSynP i q as  -> PatternSynP i q <$> rec as
      RecP kwr ci fas     -> RecP kwr ci <$> rec fas
      EqualP i es         -> EqualP i <$> rec es
      WithP i p'          -> WithP i <$> rec p'
    where
      rec :: forall b. ExprLike' b => b -> m b
      rec = recurseExprLike' g
  
instance ExprLike' a => ExprLike' (Clause' a) where
  recurseExprLike'Raw :: forall m. RecurseLikeFn' m (Clause' a)
  recurseExprLike'Raw g c@(Clause lhs spats rhs ds ca) =
    g c $ Clause <$> rec lhs <*> pure spats <*> rec rhs <*> rec ds <*> pure ca
    where
      rec :: forall b. ExprLike' b => b -> m b
      rec = recurseExprLike' g

instance ExprLike' RHS where

  recurseExprLike'Raw :: forall m. RecurseLikeFn' m RHS
  recurseExprLike'Raw g r = g r $ case r of
    RHS e c                    -> RHS <$> rec e <*> pure c
    AbsurdRHS                  -> pure r
    WithRHS x es cs            -> WithRHS x <$> rec es <*> rec cs
    RewriteRHS xes spats rhs ds-> RewriteRHS <$> rec xes <*> pure spats <*> rec rhs <*> rec ds
    where rec :: TraverseLikeRecFn' m
          rec = recurseExprLike' g

instance (ExprLike' qn, ExprLike' nm, ExprLike' p, ExprLike' e) => ExprLike' (RewriteEqn' qn nm p e) where


  recurseExprLike'Raw :: forall m. RecurseLikeFn' m (RewriteEqn' qn nm p e)
  recurseExprLike'Raw g = \case
    re@(Rewrite es)    -> g re $ Rewrite <$> recurseExprLike' g es
    iv@(Invert q pes)  -> g iv $ Invert  <$> recurseExprLike' g q  <*> recurseExprLike' g pes
    ll@(LeftLet pes)   -> g ll $ LeftLet <$> recurseExprLike' g pes
    
instance ExprLike' WhereDeclarations where


  recurseExprLike'Raw g wd@(WhereDecls a b c) =
    g wd $ WhereDecls a b <$> rec c
    where rec = recurseExprLike' g

instance ExprLike' ModuleApplication where

  recurseExprLike'Raw :: forall m. RecurseLikeFn' m ModuleApplication
  recurseExprLike'Raw g a =
    g a $ case a of
      SectionApp tel m es     -> SectionApp <$> rec tel <*> rec m <*> rec es
      RecordModuleInstance{}  -> pure a
    where rec :: TraverseLikeRecFn' m
          rec = recurseExprLike' g

instance ExprLike' Pragma where

  recurseExprLike'Raw :: forall m. RecurseLikeFn' m Pragma
  recurseExprLike'Raw g p =
    g p $ case p of
      DisplayPragma q xs e -> DisplayPragma q <$> rec xs <*> rec e
      _                    -> pure p
    where rec :: TraverseLikeRecFn' m
          rec = recurseExprLike' g

instance ExprLike' LHS where

  recurseExprLike'Raw g l@(LHS i p) = g l $ LHS i <$> rec p
    where rec = recurseExprLike' g

instance ExprLike' a => ExprLike' (LHSCore' a)   where
  recurseExprLike'Raw :: forall m. RecurseLikeFn' m (LHSCore' a)
  recurseExprLike'Raw g h =
    g h $ case h of
      LHSHead f ps         -> LHSHead f <$> rec ps
      LHSProj d focus ps   -> LHSProj d <$> rec focus <*> rec ps
      LHSWith h' wps ps    -> LHSWith  <$> rec h'    <*> rec wps <*> rec ps
    where
      rec :: forall b. ExprLike' b => b -> m b
      rec = recurseExprLike' g
      
instance ExprLike' a => ExprLike' (WithHiding a) where

instance ExprLike' SpineLHS where

  recurseExprLike'Raw g s@(SpineLHS i x ps) = g s $ SpineLHS i x <$> rec ps
    where rec = recurseExprLike' g

instance ExprLike' Declaration where

  recurseExprLike'Raw :: forall m. RecurseLikeFn' m Declaration
  recurseExprLike'Raw g d =
    g d $ case d of
      Axiom a di i mp x e         -> Axiom a di i mp x <$> rec e
      Generalize s i j x e        -> Generalize s i j x <$> rec e
      Field i x e                 -> Field i x <$> rec e
      Primitive i x e             -> Primitive i x <$> rec e
      Mutual i ds                 -> Mutual i <$> rec ds
      Section i e m tel ds        -> Section i e m <$> rec tel <*> rec ds
      Apply i e m a ci d'         -> (\a' -> Apply i e m a' ci d') <$> rec a
      Import{}                    -> pure d
      Pragma i p                  -> Pragma i <$> rec p
      Open{}                      -> pure d
      FunDef i f' cs              -> FunDef i f' <$> rec cs
      DataSig i er d' tel e       -> DataSig i er d' <$> rec tel <*> rec e
      DataDef i d' uc bs cs       -> DataDef i d' uc <$> rec bs <*> rec cs
      RecSig i er r tel e         -> RecSig i er r <$> rec tel <*> rec e
      RecDef i r uc dir bs e ds   -> RecDef i r uc dir <$> rec bs <*> rec e <*> rec ds
      PatternSynDef f' xs p       -> PatternSynDef f' xs <$> rec p
      UnquoteDecl i is xs e       -> UnquoteDecl i is xs <$> rec e
      UnquoteDef i xs e           -> UnquoteDef i xs <$> rec e
      UnquoteData i xs uc j cs e  -> UnquoteData i xs uc j cs <$> rec e
      ScopedDecl s ds             -> ScopedDecl s <$> rec ds
      UnfoldingDecl r ds          -> UnfoldingDecl r <$> rec ds
    where rec :: TraverseLikeRecFn' m
          rec = recurseExprLike' g

