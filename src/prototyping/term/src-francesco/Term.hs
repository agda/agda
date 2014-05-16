module Term where

import           Prelude.Extras                   (Eq1((==#)))
import           Bound
import qualified Bound.Name                       as Bound
import           Data.Foldable                    (Foldable)
import           Data.Traversable                 (Traversable)

import           Syntax.Abstract                  (Name)

-- Named
------------------------------------------------------------------------

-- | We use this type for bound variables of which we want to remember
-- the original name.
type Named = Bound.Name Name

named :: Name -> a -> Named a
named = Bound.Name

unNamed :: Named a -> a
unNamed (Bound.Name _ x) = x

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
    deriving (Eq, Ord, Functor, Foldable, Traversable)

instance (Eq1 term) => Eq1 (Elim term) where
    Apply t1 ==# Apply t2 = t1 ==# t2
    Proj f1  ==# Proj f2  = f1 == f2
    _        ==# _        = False

instance Bound Elim where
    Apply t    >>>= f = Apply (t >>= f)
    Proj field >>>= _ = Proj field
