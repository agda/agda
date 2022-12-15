
module Agda.Syntax.Abstract.UsedNames
  ( allUsedNames
  ) where

import Data.Foldable (foldMap)
import Data.Semigroup (Semigroup, (<>))
import Data.Set (Set)
import qualified Data.Set as Set

import Agda.Syntax.Common
import Agda.Syntax.Abstract
import Agda.Syntax.Concrete (FieldAssignment'(..))
import Agda.Utils.List1 (List1)

import Agda.Utils.Impossible

-- | All names used in an abstract expression. This is used when rendering clauses to figure out
--   which (implicit) pattern variables must be preserved. For example, the for @f : Nat → Nat@, the
--   clause @f {n} = 0@ can be printed as @f = 0@ (dropping the @n@), but @f {n} = n@ must preserve
--   the @n@.
allUsedNames :: Expr -> Set Name
allUsedNames = usedNames . boundAndUsed

data BoundAndUsedNames = BoundAndUsedNames
  { boundNames :: Set Name
  , usedNames  :: Set Name }

-- | Bound names in first argument scope over second argument.
instance Semigroup BoundAndUsedNames where
  BoundAndUsedNames bound1 used1 <> BoundAndUsedNames bound2 used2 =
    BoundAndUsedNames (bound1 <> bound2) (used1 <> Set.difference used2 bound1)

instance Monoid BoundAndUsedNames where
  mempty  = BoundAndUsedNames mempty mempty
  mappend = (<>)

singleUse :: Name -> BoundAndUsedNames
singleUse x = BoundAndUsedNames mempty (Set.singleton x)

singleBind :: Name -> BoundAndUsedNames
singleBind x = BoundAndUsedNames (Set.singleton x) mempty

noBindings :: BoundAndUsedNames -> BoundAndUsedNames
noBindings names = names{ boundNames = mempty }

-- | Bound names in first argument do *not* scope over second argument.
parB :: BoundAndUsedNames -> BoundAndUsedNames -> BoundAndUsedNames
parB (BoundAndUsedNames bound1 used1) (BoundAndUsedNames bound2 used2) =
  BoundAndUsedNames (bound1 <> bound2) (used1 <> used2)

parBindings :: (BoundAndUsed a, BoundAndUsed b) => a -> b -> BoundAndUsedNames
parBindings a b = boundAndUsed a `parB` boundAndUsed b

parBoundAndUsed :: (Foldable f, BoundAndUsed a) => f a -> BoundAndUsedNames
parBoundAndUsed = foldr parBindings mempty

class BoundAndUsed a where
  boundAndUsed :: a -> BoundAndUsedNames

  default boundAndUsed :: (a ~ f b, Foldable f, BoundAndUsed b) => a -> BoundAndUsedNames
  boundAndUsed = foldMap boundAndUsed

instance BoundAndUsed BoundAndUsedNames where
  boundAndUsed = id

instance BoundAndUsed a => BoundAndUsed (Arg a)
instance BoundAndUsed a => BoundAndUsed (Named n a)
instance BoundAndUsed a => BoundAndUsed (List1 a)
instance BoundAndUsed a => BoundAndUsed [a]
instance BoundAndUsed a => BoundAndUsed (Maybe a)

instance (BoundAndUsed a, BoundAndUsed b) => BoundAndUsed (Either a b) where
  boundAndUsed = either boundAndUsed boundAndUsed

instance BoundAndUsed ModuleName where
  boundAndUsed _ = mempty

instance (BoundAndUsed a, BoundAndUsed b) => BoundAndUsed (a, b) where
  boundAndUsed (a, b) = boundAndUsed a <> boundAndUsed b

instance BoundAndUsed Expr where
  boundAndUsed = noBindings . \ case
    Var x                  -> singleUse x
    Def'{}                 -> mempty
    Proj{}                 -> mempty
    Con{}                  -> mempty
    PatternSyn{}           -> mempty
    Macro{}                -> mempty
    Lit{}                  -> mempty
    QuestionMark{}         -> mempty
    Underscore{}           -> mempty
    Dot _ expr             -> boundAndUsed expr
    App _ expr arg         -> boundAndUsed (expr, arg)
    WithApp _ expr exprs   -> boundAndUsed (expr, exprs)
    Lam _ bind expr        -> boundAndUsed (bind, expr)
    AbsurdLam{}            -> mempty
    ExtendedLam _ _ _ _ cs -> boundAndUsed cs
    Pi _ tel expr          -> boundAndUsed (tel, expr)
    Generalized _ expr     -> boundAndUsed expr
    Fun _ arg expr         -> boundAndUsed (arg, expr)
    Let _ binds expr       -> boundAndUsed (binds, expr)
    Rec _ as               -> boundAndUsed as
    RecUpdate _ expr as    -> boundAndUsed expr <> boundAndUsed as
    ScopedExpr _ expr      -> boundAndUsed expr
    Quote{}                -> mempty
    QuoteTerm{}            -> mempty
    Unquote{}              -> mempty
    DontCare expr          -> boundAndUsed expr

instance BoundAndUsed lhs => BoundAndUsed (Clause' lhs) where
  -- Note: where declarations are ignored. We use this only on expressions coming from
  --       InternalToAbstract where there are no where decls.
  boundAndUsed Clause{ clauseLHS = lhs, clauseRHS = rhs } = boundAndUsed (lhs, rhs)

instance BoundAndUsed RHS where
  boundAndUsed = \ case
    RHS body _              -> boundAndUsed body
    AbsurdRHS               -> mempty
    WithRHS _ es cs         -> boundAndUsed (es, cs)
    RewriteRHS eqns _ rhs _ -> boundAndUsed (eqns, rhs)

instance BoundAndUsed LHS where
  boundAndUsed = boundAndUsed . lhsCore

instance BoundAndUsed e => BoundAndUsed (LHSCore' e) where
  boundAndUsed = \ case
    LHSHead _ ps       -> parBoundAndUsed ps
    LHSProj _ lhs ps   -> lhs `parBindings` parBoundAndUsed ps
    LHSWith lhs wps ps -> lhs `parBindings` parBoundAndUsed wps
                              `parBindings` parBoundAndUsed ps

instance (BoundAndUsed x, BoundAndUsed p, BoundAndUsed e) => BoundAndUsed (RewriteEqn' q x p e) where
  boundAndUsed (Rewrite es)  = boundAndUsed $ snd <$> es
  boundAndUsed (Invert _ bs) = parBoundAndUsed (namedThing <$> bs) <> boundAndUsed (nameOf <$> bs)

instance BoundAndUsed LetBinding where
  boundAndUsed = \ case   -- Note: binder last since it's not recursive
    LetBind _ _ x ty e     -> boundAndUsed ((ty, e), x)
    LetPatBind _ p e       -> boundAndUsed (e, p)
    LetApply _ _ _ app _ _ -> boundAndUsed app
    LetOpen{}              -> mempty
    LetDeclaredVariable{}  -> mempty   -- Only used for highlighting

instance BoundAndUsed LamBinding where
  boundAndUsed (DomainFree _ b) = boundAndUsed b
  boundAndUsed (DomainFull b)   = boundAndUsed b

instance BoundAndUsed TypedBinding where
  boundAndUsed (TBind _ _ bs ty) = boundAndUsed (ty, bs)
  boundAndUsed (TLet _ bs)       = boundAndUsed bs

instance BoundAndUsed name => BoundAndUsed (Binder' name) where
  boundAndUsed (Binder p x) = parBindings p x

instance BoundAndUsed BindName where
  boundAndUsed x = singleBind (unBind x)

instance BoundAndUsed e => BoundAndUsed (Pattern' e) where
  boundAndUsed = \ case
    VarP x             -> boundAndUsed x
    ConP _ _ ps        -> parBoundAndUsed ps
    ProjP{}            -> mempty
    DefP _ _ ps        -> parBoundAndUsed ps
    WildP{}            -> mempty
    AsP _ x p          -> parBindings x p
    DotP _ e           -> boundAndUsed e
    AbsurdP{}          -> mempty
    LitP{}             -> mempty
    PatternSynP _ _ ps -> parBoundAndUsed ps
    RecP _ as          -> parBoundAndUsed as
    EqualP _ eqs       -> parBoundAndUsed eqs
    WithP _ p          -> boundAndUsed p
    AnnP _ ty p        -> boundAndUsed (ty, p)

instance BoundAndUsed e => BoundAndUsed (FieldAssignment' e) where
  boundAndUsed (FieldAssignment _ e) = boundAndUsed e

instance BoundAndUsed ModuleApplication where
  boundAndUsed (SectionApp tel _ es)  = noBindings $ boundAndUsed (tel, es)
  boundAndUsed RecordModuleInstance{} = mempty

