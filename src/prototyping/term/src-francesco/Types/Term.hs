module Types.Term where

import           Bound
import qualified Bound.Name
import           Data.Foldable                    (Foldable)
import           Data.Traversable                 (Traversable)
import           Prelude.Extras                   (Eq1((==#)))
import           Data.Void                        (Void)

import           Syntax.Abstract                  (Name)

-- Terms
------------------------------------------------------------------------

-- | 'MetaVar'iables.  Globally scoped.
newtype MetaVar = MetaVar {unMetaVar :: Int}
    deriving (Eq, Ord, Show)

-- | A 'Head' heads a neutral term -- something which can't reduce
-- further.
data Head v
    = Var v
    | Def Name
    | Con Name
    | J
    | Refl
    | Meta MetaVar
    deriving (Eq, Ord, Functor, Foldable, Traversable)

instance Eq1 Head

-- | The field of a projection.
newtype Field = Field {unField :: Int}
    deriving (Eq, Ord)

-- | 'Elim's are applied to 'Head's.  They're either arguments applied
-- to functions, or projections applied to records.
data Elim term v
    = Apply (term v)
    | Proj Field
    deriving (Eq, Functor, Foldable, Traversable)

instance (Eq1 term) => Eq1 (Elim term) where
    Apply t1 ==# Apply t2 = t1 ==# t2
    Proj f1  ==# Proj f2  = f1 == f2
    _        ==# _        = False

instance Bound Elim where
    Apply t    >>>= f = Apply (t >>= f)
    Proj field >>>= _ = Proj field

data TermView abs term v
    = Lam (abs v)
    | Pi (term v) (abs v)
    | Equal (term v) (term v) (term v)
    | App (Head v) [Elim term v]
    | Set
    deriving (Eq, Functor, Foldable, Traversable)

instance (Eq1 term, Eq1 abs) => Eq1 (TermView abs term) where
    Lam body1 ==# Lam body2 =
        body1 ==# body2
    Pi domain1 codomain1 ==# Pi domain2 codomain2 =
        domain1 ==# domain2 && codomain1 ==# codomain2
    Equal type1 x1 y1 ==# Equal type2 x2 y2 =
        type1 ==# type2 && x1 ==# x2 && y1 ==# y2
    App h1 els1 ==# App h2 els2 =
        h1 == h2 && and (zipWith (==#) els1 els2)
    Set ==# Set =
        True
    _ ==# _ =
        False

-- | Type synonym useful for documentation.
type Type t v = t v

type ClosedTermView abs term = TermView abs term Void

-- Named
------------------------------------------------------------------------

-- | We use this type for bound variables of which we want to remember
-- the original name.
type Named = Bound.Name.Name Name

named :: Name -> a -> Named a
named = Bound.Name.Name

unNamed :: Named a -> a
unNamed (Bound.Name.Name _ x) = x

-- TermVar
------------------------------------------------------------------------

-- | A 'Var' with one 'Named' free variable.
type TermVar = Bound.Var (Named ())

boundTermVar :: Name -> TermVar v
boundTermVar n = B $ named n ()

type ClosedTerm t = t Void
type ClosedType t = t Void
