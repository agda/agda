{-# LANGUAGE CPP               #-}
{-# LANGUAGE FlexibleInstances #-}

-- | Generic traversal and reduce for concrete syntax,
--   in the style of "Agda.Syntax.Internal.Generic".
--
--   However, here we use the terminology of 'Data.Traversable'.

module Agda.Syntax.Concrete.Generic where

import Control.Applicative

import Data.Traversable
import Data.Monoid
import Data.Foldable

import Agda.Syntax.Common hiding (Arg)
import Agda.Syntax.Concrete

import Agda.Utils.Either

#include "undefined.h"
import Agda.Utils.Impossible

-- | Generic traversals for concrete expressions.
--
--   Note: does not go into patterns!
class ExprLike a where
  mapExpr      :: (Expr -> Expr) -> a -> a
  -- ^ This corresponds to 'map'.
  traverseExpr :: (Monad m, Applicative m) => (Expr -> m Expr) -> a -> m a
  -- ^ This corresponds to 'mapM'.
  foldExpr     :: Monoid m => (Expr -> m) -> a -> m
  -- ^ This is a reduce.

  traverseExpr = __IMPOSSIBLE__  -- TODO: implement!
  foldExpr     = __IMPOSSIBLE__  -- TODO: implement!

-- * Instances for things that do not contain expressions.

instance ExprLike Name where
  mapExpr f = id

instance ExprLike QName where
  mapExpr f = id

-- * Instances for functors.

instance ExprLike a => ExprLike (Named name a) where
  mapExpr      = fmap     . mapExpr
  traverseExpr = traverse . traverseExpr
  foldExpr     = foldMap  . foldExpr

instance ExprLike a => ExprLike (Arg a) where  -- TODO guilhem
  mapExpr      = fmap     . mapExpr
  traverseExpr = traverse . traverseExpr
  foldExpr     = foldMap  . foldExpr

instance ExprLike a => ExprLike [a] where
  mapExpr      = fmap     . mapExpr
  traverseExpr = traverse . traverseExpr
  foldExpr     = foldMap  . foldExpr

instance ExprLike a => ExprLike (Maybe a) where
  mapExpr      = fmap     . mapExpr
  traverseExpr = traverse . traverseExpr
  foldExpr     = foldMap  . foldExpr

instance ExprLike a => ExprLike (MaybePlaceholder a) where
  mapExpr      = fmap     . mapExpr
  traverseExpr = traverse . traverseExpr
  foldExpr     = foldMap  . foldExpr

instance (ExprLike a, ExprLike b) => ExprLike (Either a b) where
  mapExpr f      = mapEither (mapExpr f) (mapExpr f)
  traverseExpr f = traverseEither (traverseExpr f) (traverseExpr f)
  foldExpr f     = either (foldExpr f) (foldExpr f)

instance ExprLike a => ExprLike (TypedBinding' a) where
  mapExpr      = fmap     . mapExpr
  traverseExpr = traverse . traverseExpr
  foldExpr     = foldMap  . foldExpr

instance ExprLike a => ExprLike (RHS' a) where
  mapExpr      = fmap     . mapExpr
  traverseExpr = traverse . traverseExpr
  foldExpr     = foldMap  . foldExpr

instance ExprLike a => ExprLike (WhereClause' a) where
  mapExpr      = fmap     . mapExpr
  traverseExpr = traverse . traverseExpr
  foldExpr     = foldMap  . foldExpr

instance (ExprLike a, ExprLike b) => ExprLike (a, b) where
  mapExpr      f (x, y) = (mapExpr f x, mapExpr f y)
  traverseExpr f (x, y) = (,) <$> traverseExpr f x <*> traverseExpr f y
  foldExpr     f (x, y) = foldExpr f x `mappend` foldExpr f y

instance (ExprLike a, ExprLike b, ExprLike c) => ExprLike (a, b, c) where
  mapExpr      f (x, y, z) = (mapExpr f x, mapExpr f y, mapExpr f z)
  traverseExpr f (x, y, z) = (,,) <$> traverseExpr f x <*> traverseExpr f y <*> traverseExpr f z
  foldExpr     f (x, y, z) = foldExpr f x `mappend` foldExpr f y `mappend` foldExpr f z

-- * Interesting instances

instance ExprLike Expr where
  mapExpr f e0 = case e0 of
     Ident{}            -> f $ e0
     Lit{}              -> f $ e0
     QuestionMark{}     -> f $ e0
     Underscore{}       -> f $ e0
     RawApp r es        -> f $ RawApp r               $ mapE es
     App r e es         -> f $ App r       (mapE e)   $ mapE es
     OpApp r q ns es    -> f $ OpApp r q ns           $ mapE es
     WithApp r e es     -> f $ WithApp r   (mapE e)   $ mapE es
     HiddenArg r e      -> f $ HiddenArg r            $ mapE e
     InstanceArg r e    -> f $ InstanceArg r          $ mapE e
     Lam r bs e         -> f $ Lam r       (mapE bs)  $ mapE e
     AbsurdLam{}        -> f $ e0
     ExtendedLam r cs   -> f $ ExtendedLam r          $ mapE cs
     Fun r a b          -> f $ Fun r       (mapE a)   $ mapE b
     Pi tel e           -> f $ Pi          (mapE tel) $ mapE e
     Set{}              -> f $ e0
     Prop{}             -> f $ e0
     SetN{}             -> f $ e0
     Rec r es           -> f $ Rec r                  $ mapE es
     RecUpdate r e es   -> f $ RecUpdate r (mapE e)   $ mapE es
     Let r ds e         -> f $ Let r       (mapE ds)  $ mapE e
     Paren r e          -> f $ Paren r                $ mapE e
     Absurd{}           -> f $ e0
     As r x e           -> f $ As r x                 $ mapE e
     Dot r e            -> f $ Dot r                  $ mapE e
     ETel tel           -> f $ ETel                   $ mapE tel
     QuoteGoal r x e    -> f $ QuoteGoal r x          $ mapE e
     QuoteContext r     -> f $ e0
     Tactic r e es      -> f $ Tactic r     (mapE e)  $ mapE es
     Quote{}            -> f $ e0
     QuoteTerm{}        -> f $ e0
     Unquote{}          -> f $ e0
     DontCare e         -> f $ DontCare               $ mapE e
     Equal{}            -> f $ e0
   where mapE e = mapExpr f e

instance ExprLike FieldAssignment where
  mapExpr      f (FieldAssignment x e) = FieldAssignment x (mapExpr f e)
  traverseExpr f (FieldAssignment x e) = (\e' -> FieldAssignment x e') <$> traverseExpr f e
  foldExpr     f (FieldAssignment _ e) = foldExpr f e

instance ExprLike ModuleAssignment where
  mapExpr      f (ModuleAssignment m es i) = ModuleAssignment m (mapExpr f es) i
  traverseExpr f (ModuleAssignment m es i) = (\es' -> ModuleAssignment m es' i) <$> traverseExpr f es
  foldExpr     f (ModuleAssignment m es i) = foldExpr f es

instance ExprLike a => ExprLike (OpApp a) where
  mapExpr f e0 = case e0 of
     SyntaxBindingLambda r bs e -> SyntaxBindingLambda r (mapE bs) $ mapE e
     Ordinary                 e -> Ordinary                        $ mapE e
   where mapE e = mapExpr f e

instance ExprLike LamBinding where
  mapExpr f e0 = case e0 of
     DomainFree{}  -> e0
     DomainFull bs -> DomainFull $ mapE bs
   where mapE e = mapExpr f e

instance ExprLike TypedBindings where
  mapExpr f e0 = case e0 of
     TypedBindings r b -> TypedBindings r $ mapE b
   where mapE e = mapExpr f e

instance ExprLike LHS where
  mapExpr f e0 = case e0 of
     LHS    ps wps res wes -> LHS    ps wps (mapE res) $ mapE wes
     Ellipsis r ps res wes -> Ellipsis r ps (mapE res) $ mapE wes
   where mapE e = mapExpr f e

instance ExprLike ModuleApplication where
  mapExpr f e0 = case e0 of
     SectionApp r bs e -> SectionApp r (mapE bs) $ mapE e
     RecordModuleIFS{} -> e0
   where mapE e = mapExpr f e

instance ExprLike Declaration where
  mapExpr f e0 = case e0 of
     TypeSig ai x e            -> TypeSig ai x                         $ mapE e
     Field x e                 -> Field x                              $ mapE e
     FunClause lhs rhs wh      -> FunClause (mapE lhs) (mapE rhs)      $ mapE wh
     DataSig r ind x bs e      -> DataSig r ind x (mapE bs)            $ mapE e
     Data r ind n bs e cs      -> Data r ind n (mapE bs) (mapE e)      $ mapE cs
     RecordSig r ind bs e      -> RecordSig r ind (mapE bs)            $ mapE e
     Record r n ind eta c tel e ds -> Record r n ind eta c (mapE tel) (mapE e) $ mapE ds
     Infix{}                   -> e0
     Syntax{}                  -> e0
     PatternSyn{}              -> e0
     Mutual    r ds            -> Mutual    r                          $ mapE ds
     Abstract  r ds            -> Abstract  r                          $ mapE ds
     Private   r ds            -> Private   r                          $ mapE ds
     InstanceB r ds            -> InstanceB r                          $ mapE ds
     Macro     r ds            -> Macro     r                          $ mapE ds
     Postulate r ds            -> Postulate r                          $ mapE ds
     Primitive r ds            -> Primitive r                          $ mapE ds
     Open{}                    -> e0
     Import{}                  -> e0
     ModuleMacro r n es op dir -> ModuleMacro r n (mapE es) op dir
     Module r n tel ds         -> Module r n (mapE tel)                $ mapE ds
     UnquoteDecl r x e         -> UnquoteDecl r x (mapE e)
     UnquoteDef r x e          -> UnquoteDef r x (mapE e)
     Pragma{}                  -> e0
   where mapE e = mapExpr f e

{- Template

instance ExprLike a where
  mapExpr f e0 = case e0 of
   where mapE e = mapExpr f e
-}
