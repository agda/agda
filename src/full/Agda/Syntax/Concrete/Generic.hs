{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE NoMonoLocalBinds #-}  -- counteract MonoLocalBinds implied by TypeFamilies

-- | Generic traversal and reduce for concrete syntax,
--   in the style of "Agda.Syntax.Internal.Generic".
--
--   However, here we use the terminology of 'Data.Traversable'.

module Agda.Syntax.Concrete.Generic where

import Data.Bifunctor

import Agda.Syntax.Common
import Agda.Syntax.Concrete

import Agda.Utils.Either
import Agda.Utils.List1 (List1)

import Agda.Utils.Impossible

-- | Generic traversals for concrete expressions.
--
--   Note: does not go into patterns!
class ExprLike a where
  mapExpr :: (Expr -> Expr) -> a -> a
  -- ^ This corresponds to 'map'.

  foldExpr :: Monoid m => (Expr -> m) -> a -> m
  -- ^ This corresponds to 'foldMap'.

  traverseExpr :: Monad m => (Expr -> m Expr) -> a -> m a
  -- ^ This corresponds to 'mapM'.

  default mapExpr :: (Functor t, ExprLike b, t b ~ a) => (Expr -> Expr) -> a -> a
  mapExpr = fmap . mapExpr

  default foldExpr
    :: (Monoid m, Foldable t, ExprLike b, t b ~ a)
    => (Expr -> m) -> a -> m
  foldExpr = foldMap . foldExpr

  default traverseExpr
    :: (Monad m, Traversable t, ExprLike b, t b ~ a)
    => (Expr -> m Expr) -> a -> m a
  traverseExpr = traverse . traverseExpr


-- * Instances for things that do not contain expressions.

instance ExprLike () where
  mapExpr _      = id
  foldExpr _ _   = mempty
  traverseExpr _ = return

instance ExprLike Name where
  mapExpr _      = id
  foldExpr _ _   = mempty
  traverseExpr _ = return

instance ExprLike QName where
  mapExpr _      = id
  foldExpr _ _   = mempty
  traverseExpr _ = return

instance ExprLike Bool where
  mapExpr _      = id
  foldExpr _ _   = mempty
  traverseExpr _ = return

-- * Instances for collections and decorations.

instance ExprLike a => ExprLike [a]
instance ExprLike a => ExprLike (List1 a)
instance ExprLike a => ExprLike (Maybe a)

instance ExprLike a => ExprLike (Arg a)
instance ExprLike a => ExprLike (Named name a)
instance ExprLike a => ExprLike (WithHiding a)

instance ExprLike a => ExprLike (MaybePlaceholder a)
instance ExprLike a => ExprLike (RHS' a)
instance ExprLike a => ExprLike (TypedBinding' a)
instance ExprLike a => ExprLike (WhereClause' a)

instance (ExprLike a, ExprLike b) => ExprLike (Either a b) where
  mapExpr f      = bimap (mapExpr f) (mapExpr f)
  traverseExpr f = traverseEither (traverseExpr f) (traverseExpr f)
  foldExpr f     = either (foldExpr f) (foldExpr f)

instance (ExprLike a, ExprLike b) => ExprLike (a, b) where
  mapExpr      f (x, y) = (mapExpr f x, mapExpr f y)
  traverseExpr f (x, y) = (,) <$> traverseExpr f x <*> traverseExpr f y
  foldExpr     f (x, y) = foldExpr f x `mappend` foldExpr f y

instance (ExprLike a, ExprLike b, ExprLike c) => ExprLike (a, b, c) where
  mapExpr      f (x, y, z) = (mapExpr f x, mapExpr f y, mapExpr f z)
  traverseExpr f (x, y, z) = (,,) <$> traverseExpr f x <*> traverseExpr f y <*> traverseExpr f z
  foldExpr     f (x, y, z) = foldExpr f x `mappend` foldExpr f y `mappend` foldExpr f z

instance (ExprLike a, ExprLike b, ExprLike c, ExprLike d) => ExprLike (a, b, c, d) where
  mapExpr      f (x, y, z, w) = (mapExpr f x, mapExpr f y, mapExpr f z, mapExpr f w)
  traverseExpr f (x, y, z, w) = (,,,) <$> traverseExpr f x <*> traverseExpr f y <*> traverseExpr f z <*> traverseExpr f w
  foldExpr     f (x, y, z, w) = foldExpr f x `mappend` foldExpr f y `mappend` foldExpr f z `mappend` foldExpr f w

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
     Fun r a b          -> f $ Fun r     (mapE <$> a) $ mapE b
     Pi tel e           -> f $ Pi          (mapE tel) $ mapE e
     Set{}              -> f $ e0
     Prop{}             -> f $ e0
     SetN{}             -> f $ e0
     PropN{}            -> f $ e0
     Rec r es           -> f $ Rec r                  $ mapE es
     RecUpdate r e es   -> f $ RecUpdate r (mapE e)   $ mapE es
     Let r ds e         -> f $ Let r       (mapE ds)  $ mapE e
     Paren r e          -> f $ Paren r                $ mapE e
     IdiomBrackets r es -> f $ IdiomBrackets r        $ mapE es
     DoBlock r ss       -> f $ DoBlock r              $ mapE ss
     Absurd{}           -> f $ e0
     As r x e           -> f $ As r x                 $ mapE e
     Dot r e            -> f $ Dot r                  $ mapE e
     DoubleDot r e      -> f $ DoubleDot r            $ mapE e
     ETel tel           -> f $ ETel                   $ mapE tel
     Tactic r e         -> f $ Tactic r     (mapE e)
     Quote{}            -> f $ e0
     QuoteTerm{}        -> f $ e0
     Unquote{}          -> f $ e0
     DontCare e         -> f $ DontCare               $ mapE e
     Equal{}            -> f $ e0
     Ellipsis{}         -> f $ e0
     Generalized e      -> f $ Generalized            $ mapE e
   where mapE e = mapExpr f e

  foldExpr     = __IMPOSSIBLE__
  traverseExpr = __IMPOSSIBLE__

instance ExprLike FieldAssignment where
  mapExpr      f (FieldAssignment x e) = FieldAssignment x (mapExpr f e)
  traverseExpr f (FieldAssignment x e) = (\e' -> FieldAssignment x e') <$> traverseExpr f e
  foldExpr     f (FieldAssignment _ e) = foldExpr f e

instance ExprLike ModuleAssignment where
  mapExpr      f (ModuleAssignment m es i) = ModuleAssignment m (mapExpr f es) i
  traverseExpr f (ModuleAssignment m es i) = (\es' -> ModuleAssignment m es' i) <$> traverseExpr f es
  foldExpr     f (ModuleAssignment m es i) = foldExpr f es

instance ExprLike a => ExprLike (OpApp a) where
  mapExpr f = \case
     SyntaxBindingLambda r bs e -> SyntaxBindingLambda r (mapE bs) $ mapE e
     Ordinary                 e -> Ordinary                        $ mapE e
   where mapE e = mapExpr f e
  foldExpr     = __IMPOSSIBLE__
  traverseExpr = __IMPOSSIBLE__

instance ExprLike LamBinding where
  mapExpr f = \case
     e@DomainFree{}-> e
     DomainFull bs -> DomainFull $ mapE bs
   where mapE e = mapExpr f e
  foldExpr     = __IMPOSSIBLE__
  traverseExpr = __IMPOSSIBLE__

instance ExprLike LHS where
  mapExpr f = \case
     LHS ps res wes ell -> LHS ps (mapE res) (mapE wes) ell
   where mapE e = mapExpr f e
  foldExpr     = __IMPOSSIBLE__
  traverseExpr = __IMPOSSIBLE__

instance (ExprLike qn, ExprLike e) => ExprLike (RewriteEqn' qn p e) where
  mapExpr f = \case
    Rewrite es    -> Rewrite (mapExpr f es)
    Invert qn pes -> Invert qn (fmap (mapExpr f <$>) pes)
  foldExpr     = __IMPOSSIBLE__
  traverseExpr = __IMPOSSIBLE__

instance ExprLike LamClause where
  mapExpr f (LamClause ps rhs ca) = LamClause ps (mapExpr f rhs) ca
  foldExpr     = __IMPOSSIBLE__
  traverseExpr = __IMPOSSIBLE__

instance ExprLike DoStmt where
  mapExpr f (DoBind r p e cs) = DoBind r p (mapExpr f e) (mapExpr f cs)
  mapExpr f (DoThen e)        = DoThen (mapExpr f e)
  mapExpr f (DoLet r ds)      = DoLet r (mapExpr f ds)

  foldExpr     = __IMPOSSIBLE__
  traverseExpr = __IMPOSSIBLE__

instance ExprLike ModuleApplication where
  mapExpr f = \case
     SectionApp r bs e -> SectionApp r (mapE bs) $ mapE e
     e@RecordModuleInstance{} -> e
   where mapE e = mapExpr f e
  foldExpr     = __IMPOSSIBLE__
  traverseExpr = __IMPOSSIBLE__

instance ExprLike Declaration where
  mapExpr f = \case
     TypeSig ai t x e          -> TypeSig ai (mapE t) x (mapE e)
     FieldSig i t n e          -> FieldSig i (mapE t) n (mapE e)
     Field r fs                -> Field r                              $ map (mapExpr f) fs
     FunClause lhs rhs wh ca   -> FunClause (mapE lhs) (mapE rhs) (mapE wh) (mapE ca)
     DataSig r x bs e          -> DataSig r x (mapE bs)                $ mapE e
     DataDef r n bs cs         -> DataDef r n (mapE bs)                $ mapE cs
     Data r n bs e cs          -> Data r n (mapE bs) (mapE e)          $ mapE cs
     RecordSig r ind bs e      -> RecordSig r ind (mapE bs)            $ mapE e
     RecordDef r n ind eta c tel ds -> RecordDef r n ind eta c (mapE tel) $ mapE ds
     Record r n ind eta c tel e ds  -> Record r n ind eta c (mapE tel) (mapE e) $ mapE ds
     e@Infix{}                 -> e
     e@Syntax{}                -> e
     e@PatternSyn{}            -> e
     Mutual    r ds            -> Mutual    r                          $ mapE ds
     Abstract  r ds            -> Abstract  r                          $ mapE ds
     Private   r o ds          -> Private   r o                        $ mapE ds
     InstanceB r ds            -> InstanceB r                          $ mapE ds
     Macro     r ds            -> Macro     r                          $ mapE ds
     Postulate r ds            -> Postulate r                          $ mapE ds
     Primitive r ds            -> Primitive r                          $ mapE ds
     Generalize r ds           -> Generalize r                         $ mapE ds
     e@Open{}                  -> e
     e@Import{}                -> e
     ModuleMacro r n es op dir -> ModuleMacro r n (mapE es) op dir
     Module r n tel ds         -> Module r n (mapE tel)                $ mapE ds
     UnquoteDecl r x e         -> UnquoteDecl r x (mapE e)
     UnquoteDef r x e          -> UnquoteDef r x (mapE e)
     e@Pragma{}                -> e
   where mapE e = mapExpr f e

  foldExpr     = __IMPOSSIBLE__
  traverseExpr = __IMPOSSIBLE__


{- Template

instance ExprLike a where
  mapExpr f = \case
    where mapE e = mapExpr f e
  foldExpr     = __IMPOSSIBLE__
  traverseExpr = __IMPOSSIBLE__

-}
