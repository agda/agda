
-- | Generic traversal and reduce for concrete syntax,
--   in the style of "Agda.Syntax.Internal.Generic".
--
--   However, here we use the terminology of 'Data.Traversable'.

module Agda.Syntax.Concrete.Generic where

import Data.Bifunctor

import Agda.Syntax.Common
import Agda.Syntax.Concrete

import Agda.Utils.Either

import Agda.Utils.Impossible

-- | Generic traversals for concrete expressions.
--
--   Note: does not go into patterns!
class ExprLike a where
  mapExpr :: (Expr -> Expr) -> a -> a
  -- ^ This corresponds to 'map'.

  traverseExpr :: Monad m => (Expr -> m Expr) -> a -> m a
  -- ^ This corresponds to 'mapM'.

  foldExpr :: Monoid m => (Expr -> m) -> a -> m
  -- ^ This is a reduce.

  traverseExpr = __IMPOSSIBLE__  -- TODO: implement!
  foldExpr     = __IMPOSSIBLE__  -- TODO: implement!

-- * Instances for things that do not contain expressions.

instance ExprLike Name where
  mapExpr f = id

instance ExprLike QName where
  mapExpr f = id

instance ExprLike Bool where
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
  mapExpr f      = bimap (mapExpr f) (mapExpr f)
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
     ETel tel           -> f $ ETel                   $ mapE tel
     QuoteGoal r x e    -> f $ QuoteGoal r x          $ mapE e
     QuoteContext r     -> f $ e0
     Tactic r e es      -> f $ Tactic r     (mapE e)  $ mapE es
     Quote{}            -> f $ e0
     QuoteTerm{}        -> f $ e0
     Unquote{}          -> f $ e0
     DontCare e         -> f $ DontCare               $ mapE e
     Equal{}            -> f $ e0
     Ellipsis{}         -> f $ e0
     Generalized e      -> f $ Generalized            $ mapE e
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

instance ExprLike LHS where
  mapExpr f e0 = case e0 of
     LHS ps res wes -> LHS ps (mapE res) $ mapE wes
   where mapE e = mapExpr f e

instance ExprLike e => ExprLike (RewriteEqn' p e) where
  mapExpr f = \case
    Rewrite es -> Rewrite (mapExpr f es)
    Invert pes -> Invert (map (mapExpr f <$>) pes)

instance ExprLike LamClause where
  mapExpr f (LamClause lhs rhs wh ca) =
    LamClause (mapExpr f lhs) (mapExpr f rhs) (mapExpr f wh) (mapExpr f ca)

instance ExprLike DoStmt where
  mapExpr f (DoBind r p e cs) = DoBind r p (mapExpr f e) (mapExpr f cs)
  mapExpr f (DoThen e)        = DoThen (mapExpr f e)
  mapExpr f (DoLet r ds)      = DoLet r (mapExpr f ds)

instance ExprLike ModuleApplication where
  mapExpr f e0 = case e0 of
     SectionApp r bs e -> SectionApp r (mapE bs) $ mapE e
     RecordModuleInstance{} -> e0
   where mapE e = mapExpr f e

instance ExprLike Declaration where
  mapExpr f = \case
     TypeSig ai x e            -> TypeSig ai x                         $ mapE e
     FieldSig i n e            -> FieldSig i n                         $ mapE e
     Field r fs                -> Field r                              $ map (mapExpr f) fs
     FunClause lhs rhs wh ca   -> FunClause (mapE lhs) (mapE rhs) (mapE wh) (mapE ca)
     DataSig r ind x bs e      -> DataSig r ind x (mapE bs)            $ mapE e
     DataDef r ind n bs cs     -> DataDef r ind n (mapE bs)            $ mapE cs
     Data r ind n bs e cs      -> Data r ind n (mapE bs) (mapE e)      $ mapE cs
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

{- Template

instance ExprLike a where
  mapExpr f e0 = case e0 of
   where mapE e = mapExpr f e
-}
