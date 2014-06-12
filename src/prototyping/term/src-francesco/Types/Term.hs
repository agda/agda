{-# LANGUAGE OverloadedStrings #-}
module Types.Term where

import           Prelude                          hiding (pi, foldr)

import           Bound                            hiding (instantiate)
import qualified Bound.Name                       as Bound
import           Data.Foldable                    (Foldable, foldr)
import           Data.Traversable                 (Traversable)
import           Prelude.Extras                   (Eq1((==#)))
import           Data.Void                        (Void, absurd)
import           Data.Monoid                      (mempty, (<>), mconcat)
import qualified Data.HashSet                     as HS
import           Control.Monad                    (liftM)
import           Data.Typeable                    (Typeable)
import           Data.Hashable                    (Hashable)
import           Data.Maybe                       (fromMaybe)
import           Control.Applicative              (Applicative, pure, (<*>))
import qualified Data.Set                         as Set

import qualified Text.PrettyPrint.Extended        as PP
import           Syntax.Abstract                  (Name)
import           Syntax.Abstract.Pretty           ()

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
getName_ = fromMaybe "_" . getName


-- 'IsVar' variables
------------------------------------------------------------------------

class VarName v where
    varName :: v -> Name

class VarIndex v where
    varIndex :: v -> Int

class (Eq v, Ord v, Typeable v, VarName v, VarIndex v) => IsVar v

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
    varIndex (B v) = unNamed v
    varIndex (F v) = absurd v

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

-- Useful type synonyms
------------------------------------------------------------------------

type Type (t :: * -> *) = t
type Term (t :: * -> *) = t

-- Terms
------------------------------------------------------------------------

-- | A 'Head' heads a neutral term -- something which can't reduce
-- further.
data Head v
    = Var v
    | Def Name
    | J
    | Meta MetaVar
    deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

instance Eq1 Head

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

-- | The 'TermView' lets us pattern match on terms.  The actual
-- implementation of terms might be different, but we must be able to
-- get a 'TermView' out of it.  See 'View'.
data TermView term v
    = Lam (Abs term v)
    | Pi (term v) (Abs term v)
    | Equal (term v) (term v) (term v)
    | Refl
    | Con Name [term v]
    | Set
    | App (Head v) [Elim term v]

deriving instance (IsTerm term) => Functor (TermView term)
deriving instance (IsTerm term) => Foldable (TermView term)
deriving instance (IsTerm term) => Traversable (TermView term)

instance (Eq v, IsTerm t) => Eq (TermView t v) where
    t1 == t2 = t1 ==# t2

instance (IsTerm term) => Eq1 (TermView term) where
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

type ClosedTermView term = TermView term Void

-- Term typeclass
------------------------------------------------------------------------

-- | Things that contain 'MetaVar's.
class MetaVars t where
    metaVars :: t v -> HS.HashSet MetaVar

    default metaVars :: (View t, HasAbs t) => t v -> HS.HashSet MetaVar
    metaVars t = case view t of
        Lam body           -> metaVars (fromAbs body)
        Pi domain codomain -> metaVars domain <> metaVars (fromAbs codomain)
        Equal type_ x y    -> metaVars type_ <> metaVars x <> metaVars y
        App h elims        -> metaVars h <> mconcat (map metaVars elims)
        Set                -> mempty
        Refl               -> mempty
        Con _ elims        -> mconcat (map metaVars elims)

instance MetaVars Head where
    metaVars (Meta mv) = HS.singleton mv
    metaVars _         = mempty

instance MetaVars t => MetaVars (Elim t) where
    metaVars (Apply t)  = metaVars t
    metaVars (Proj _ _) = mempty

-- | Abstractions.
class (Monad t) => HasAbs t where
    data Abs t :: * -> *

    -- | Transform a term scoped over something into an abstraction.
    toAbs   :: t (TermVar v) -> Abs t v
    -- | Transform an abstraction into a term scoped over something.
    fromAbs :: Abs t v -> t (TermVar v)

    -- Methods present in the typeclass so that the instances can
    -- support a faster version.

    weaken :: t v -> Abs t v
    weaken = toAbs . liftM F

    instantiate :: Abs t v -> t v -> t v
    instantiate abs' t = fromAbs abs' >>= \v -> case v of
        B _  -> t
        F v' -> return v'

    abstract :: (Eq v, VarName v) => v -> t v -> Abs t v
    abstract v t = toAbs $ liftM f t
      where
        f v' = if v == v' then boundTermVar (varName v) else F v'

class View t where
    unview :: TermView t v -> t v
    view   :: t v -> TermView t v

class ( Eq1 t,       Functor t,       Foldable t,       Traversable t, Monad t, Typeable t
      , Eq1 (Abs t), Functor (Abs t), Foldable (Abs t), Traversable (Abs t)
      , View t, MetaVars t, HasAbs t
      ) => IsTerm t

deriving instance Typeable Abs

-- Term utils
-------------

lam :: View t => Abs t v -> t v
lam body = unview $ Lam body

pi :: View t => t v -> Abs t v -> t v
pi domain codomain = unview $ Pi domain codomain

equal :: View t => t v -> t v -> t v -> t v
equal type_ x y = unview $ Equal type_ x y

app :: View t => Head v -> [Elim t v] -> t v
app h elims = unview $ App h elims

set :: View t => t v
set = unview Set

var :: View t => v -> t v
var v = unview (App (Var v) [])

metaVar :: View t => MetaVar -> [Elim t v] -> t v
metaVar mv = unview . App (Meta mv)

def :: View t => Name -> [Elim t v] -> t v
def f = unview . App (Def f)

con :: View t => Name -> [t v] -> t v
con c args = unview (Con c args)

refl :: View t => t v
refl = unview Refl

renderView :: (IsVar v, IsTerm t) => t v -> String
renderView = PP.render . view

prettyView :: (IsVar v, IsTerm t) => t v -> PP.Doc
prettyView = PP.pretty . view

-- TermTraverse
------------------------------------------------------------------------

-- | Useful 'Applicative' when traversing terms, and we want to either
-- succeed ('TTOK'), or fail ('TTFail'), or collect a bunch of metas
-- ('TTMetaVars').  See instance definition for semantics.
data TermTraverse err a
    = TTOK a
    | TTFail err
    | TTMetaVars (Set.Set MetaVar)
    deriving (Functor)

instance Applicative (TermTraverse err) where
    pure = TTOK

    TTOK f          <*> TTOK x           = TTOK (f x)
    TTOK _          <*> TTMetaVars mvs   = TTMetaVars mvs
    TTOK _          <*> TTFail v         = TTFail v
    TTMetaVars mvs  <*> TTOK _           = TTMetaVars mvs
    TTMetaVars mvs1 <*> TTMetaVars mvs2  = TTMetaVars (mvs1 <> mvs2)
    TTMetaVars _    <*> TTFail v         = TTFail v
    TTFail v        <*> _                = TTFail v

-- Pretty printing
------------------------------------------------------------------------

instance (IsVar v) => PP.Pretty (Head v) where
    pretty (Var v)   = PP.pretty (varIndex v) <> "#" <> PP.pretty (varName v)
    pretty (Def f)   = PP.pretty f
    pretty J         = PP.text "J"
    pretty (Meta mv) = PP.pretty mv

instance (IsTerm t, IsVar v) => PP.Pretty (Elim t v) where
    prettyPrec p (Apply e)  = PP.prettyPrec p $ view e
    prettyPrec _ (Proj n _) = PP.text $ show n

instance (IsTerm t, IsVar v) => PP.Pretty (TermView t v) where
  prettyPrec p t = case t of
    Set ->
      PP.text "Set"
    Equal a x y ->
      PP.prettyApp p (PP.text "_==_") [view a, view x, view y]
    Pi a0 b0 ->
      let a   = view a0
          b   = view $ fromAbs b0
          mbN = getName b
      in PP.condParens (p > 0) $
          PP.sep [ (PP.parens $ case mbN of
                      Nothing -> PP.pretty a
                      Just n  -> PP.pretty n <> PP.text " : " <> PP.pretty a) PP.<+>
                   PP.text "->"
                 , PP.nest 2 $ PP.pretty b
                 ]
    Lam b0 ->
      let b = view $ fromAbs b0
          n = getName_ b
      in PP.condParens (p > 0) $
         PP.sep [ PP.text "\\" <> PP.pretty n <> PP.text " ->"
                , PP.nest 2 $ PP.pretty b
                ]
    App h es ->
      PP.prettyApp p (PP.pretty h) es
    Refl ->
      PP.text "refl"
    Con dataCon args ->
      PP.prettyApp p (PP.pretty dataCon) (map view args)
