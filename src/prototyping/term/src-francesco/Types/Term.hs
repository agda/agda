module Types.Term where

import           Prelude                          hiding (foldr)

import           Bound
import qualified Bound.Name
import           Data.Foldable                    (Foldable, foldr)
import           Data.Traversable                 (Traversable)
import           Prelude.Extras                   (Eq1((==#)))
import           Data.Void                        (Void, absurd)
import           Data.Maybe                       (fromMaybe)
import           Data.Monoid                      ((<>))
import           Data.Hashable                    (Hashable)

import qualified Text.PrettyPrint.Extended        as PP
import qualified Syntax.Abstract                  as A
import           Syntax.Abstract                  (Name)
import           Syntax.Abstract.Pretty           ()

-- Terms
------------------------------------------------------------------------

-- | 'MetaVar'iables.  Globally scoped.
newtype MetaVar = MetaVar {unMetaVar :: Int}
    deriving (Eq, Ord, Show, Hashable)

instance PP.Pretty MetaVar where
    prettyPrec _ (MetaVar mv) = PP.text ("_" ++ show mv)

-- | A 'Head' heads a neutral term -- something which can't reduce
-- further.
data Head v
    = Var v
    | Def Name
    | Con Name
    | J
    | Refl
    | Meta MetaVar
    deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

instance (DeBruijn v) => PP.Pretty (Head v) where
    pretty (Var v) = PP.text (show ix ++ "#") <> PP.pretty name
      where (Bound.Name.Name name ix) = varIndex v
    pretty (Def f)   = PP.pretty f
    pretty (Con c)   = PP.pretty c
    pretty J         = PP.text "J"
    pretty Refl      = PP.text "refl"
    pretty (Meta mv) = PP.pretty mv

instance Eq1 Head

-- | The field of a projection.
newtype Field = Field {unField :: Int}
    deriving (Eq, Ord, Show)

-- | 'Elim's are applied to 'Head's.  They're either arguments applied
-- to functions, or projections applied to records.
data Elim term v
    = Apply (term v)
    | Proj Name Field
    deriving (Show, Eq, Functor, Foldable, Traversable)

instance (Eq1 term) => Eq1 (Elim term) where
    Apply t1   ==# Apply t2   = t1 ==# t2
    Proj n1 f1 ==# Proj n2 f2 = n1 == n2 && f1 == f2
    _          ==# _          = False

instance Bound Elim where
    Apply t      >>>= f = Apply (t >>= f)
    Proj n field >>>= _ = Proj n field

instance (PP.Pretty (term v), DeBruijn v) => PP.Pretty (Elim term v) where
    prettyPrec p (Apply e)  = PP.prettyPrec p e
    prettyPrec _ (Proj n x) = PP.text $ "." ++ show n ++ "-" ++ show x

data TermView abs term v
    = Lam (abs v)
    | Pi (term v) (abs v)
    | Equal (term v) (term v) (term v)
    | App (Head v) [Elim term v]
    | Set
    deriving (Show, Eq, Functor, Foldable, Traversable)

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
type TermVar = Var (Named ())

boundTermVar :: Name -> TermVar v
boundTermVar n = B $ named n ()

type Closed t = t Void

absName :: Foldable t => t (TermVar v) -> Name
absName = fromMaybe (A.name "_") . foldr f Nothing
  where
    f _     (Just n) = Just n
    f (B v) Nothing  = Just (Bound.Name.name v)
    f (F _) Nothing  = Nothing

class DeBruijn v where
    varIndex :: v -> Named Int

instance DeBruijn Void where
    varIndex = absurd

-- This instance is used for 'ClauseBody's.
instance DeBruijn (Var (Named Int) Void) where
    varIndex (B n) = n
    varIndex (F v) = absurd v

instance DeBruijn v => DeBruijn (Var (Named ()) v) where
    varIndex (B v) = Bound.Name.Name (Bound.Name.name v) 0
    varIndex (F v) = fmap (+ 1) (varIndex v)
