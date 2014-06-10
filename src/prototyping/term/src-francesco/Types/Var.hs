module Types.Var where

import           Prelude                          hiding (foldr)

import           Bound
import qualified Bound.Name                       as Bound
import           Data.Void                        (Void, absurd)
import           Data.Foldable                    (Foldable, foldr)
import           Data.Maybe                       (fromMaybe)
import           Data.Typeable                    (Typeable)
import           Data.Monoid                      ((<>))

import qualified Syntax.Abstract                  as A
import           Syntax.Abstract                  (Name)
import           Syntax.Abstract.Pretty           ()
import qualified Text.PrettyPrint.Extended        as PP
import           Data.Hashable                    (Hashable)

-- Named
------------------------------------------------------------------------

-- | We use this type for bound variables of which we want to remember
-- the original name.
type Named = Bound.Name Name

named :: Name -> a -> Named a
named = Bound.Name

unNamed :: Named a -> a
unNamed (Bound.Name _ x) = x

-- TermVar
------------------------------------------------------------------------

-- | A 'Var' with one 'Named' free variable.
type TermVar = Var (Named ())

boundTermVar :: Name -> TermVar v
boundTermVar n = B $ named n ()

type Closed t = t Void

getName :: Foldable t => t (TermVar v) -> Maybe Name
getName = foldr f Nothing
  where
    f _     (Just n) = Just n
    f (B v) Nothing  = Just (Bound.name v)
    f (F _) Nothing  = Nothing

getName_ :: Foldable t => t (TermVar v) -> Name
getName_ = fromMaybe (A.name "_") . getName

-- 'IsVar' variables
------------------------------------------------------------------------

class VarName v where
    varName :: v -> A.Name

class VarIndex v where
    varIndex :: v -> Int

class (Eq v, Typeable v, VarName v, VarIndex v) => IsVar v

prettyVar :: (IsVar v) => v -> PP.Doc
prettyVar v = PP.text (show (varIndex v) ++ "#") <> PP.pretty (varName v)

instance VarName Void where
    varName = absurd

instance VarIndex Void where
    varIndex = absurd

instance IsVar Void

instance (VarName v) => VarName (Var (Named a) v) where
    varName (B v) = Bound.name v
    varName (F v) = varName v

instance (VarIndex v) => VarIndex (Var (Named ()) v) where
    varIndex (B _) = 0
    varIndex (F v) = 1 + varIndex v

instance VarIndex (Var (Named Int) Void) where
    varIndex (B (Bound.Name _ i)) = i
    varIndex (F v)                = absurd v

instance (IsVar v) => IsVar (Var (Named ()) v) where

instance IsVar (Var (Named Int) Void) where

instance VarName Name where
    varName = id

-- Record 'Field's
------------------------------------------------------------------------

-- | The field of a projection.
newtype Field = Field {unField :: Int}
    deriving (Eq, Ord, Show)

-- 'MetaVar'iables
------------------------------------------------------------------------

-- | 'MetaVar'iables.  Globally scoped.
newtype MetaVar = MetaVar {unMetaVar :: Int}
    deriving (Eq, Ord, Hashable)

instance PP.Pretty MetaVar where
    prettyPrec _ = PP.text . show

instance Show MetaVar where
   show (MetaVar mv) = "_" ++ show mv
