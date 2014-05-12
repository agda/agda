{-# LANGUAGE DeriveFunctor  #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE GADTs #-}
module Term.Types
    ( -- * Named things
      Named
    , named
    , unNamed
      -- * Base 'Term'
    , TermScope
    , Term(..)
    , Type
    , ClosedTerm
    , ClosedType
    , MetaVar(..)
    , Head(..)
    , Field(..)
    , unField
    , Elim_(..)
    , Elim
    , eliminate
      -- * 'Clause'
    , Clause(..)
    , ClauseBody
    , Pattern(..)
      -- * 'Telescope'
    , Telescope(..)
    , ClosedTelescope
      -- * 'Definition'
    , Definition(..)
    , ConstantKind(..)
      -- * 'Context'
    , Context(..)
    , contextLookup
    , contextApp
    , contextPi
    ) where

import Prelude hiding (pi)

import           Bound
import qualified Bound.Name                       as Bound
import           Prelude.Extras                   (Eq1((==#)), Ord1(compare1))
import           Data.Foldable                    (Foldable)
import           Data.Traversable                 (Traversable)
import           Data.Void                        (Void, absurd)

import           Syntax.Abstract                  (Name)

-- Base terms
------------------------------------------------------------------------

-- | We use this type for bound variables of which we want to remember
-- the original name.
type Named = Bound.Name Name

named :: Name -> a -> Named a
named = Bound.Name

unNamed :: Named a -> a
unNamed (Bound.Name _ x) = x

-- | Something abstracting over 1 term.
type TermScope = Scope (Named ())

-- | Base term type.
data Term v
    = Lam (TermScope Term v)
    | Pi (Term v) (TermScope Term v)
    | Equal (Term v) (Term v) (Term v)
    | App (Head v) [Elim v]
    | Set
    deriving (Eq, Ord, Functor, Foldable, Traversable)

instance Eq1 Term
instance Ord1 Term

-- | A 'Type' is a 'Term', but the synonym helps documenting.
type Type = Term

-- | A 'Term' with no free variables.
type ClosedTerm = Term Void
type ClosedType = Type Void

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
instance Ord1 Head

-- | The field of a projection.  We keep the name around for nicer
-- pretty-printing.
newtype Field = Field (Named Int)
    deriving (Eq, Ord)

unField :: Field -> Int
unField (Field namedI) = unNamed namedI

-- | 'Elim's are applied to 'Head's.  They're either arguments applied
-- to functions, or projections applied to records.
data Elim_ t v
    = Apply (t v)
    | Proj Field
    deriving (Eq, Ord, Functor, Foldable, Traversable)

type Elim = Elim_ Term

instance (Eq1 t) => Eq1 (Elim_ t) where
    Apply t1  ==# Apply t2  = t1 ==# t2
    Proj  pi1 ==# Proj  pi2 = pi1 == pi2
    _         ==# _         = False

instance (Ord1 t) => Ord1 (Elim_ t) where
    compare1 (Apply t1) (Apply t2) = compare1 t1 t2
    compare1 (Apply _)  (Proj _)   = LT
    compare1 (Proj pi1) (Proj pi2) = compare pi1 pi2
    compare1 (Proj _)   (Apply _)  = GT

instance Bound Elim_ where
    Apply t     >>>=  f = Apply (t >>= f)
    Proj  field >>>= _f = Proj field

-- Monad instance
-----------------

instance Monad Term where
    return v = App (Var v) []

    Lam body           >>=  f = Lam (body >>>= f)
    Pi domain codomain >>=  f = Pi (domain >>= f) (codomain >>>= f)
    Equal type_ x y    >>=  f = Equal (type_ >>= f) (x >>= f) (y >>= f)
    Set                >>= _f = Set
    App h       elims  >>=  f =
        case h of
          Var v   -> eliminate (f v) elims'
          Def n   -> App (Def n)   elims'
          Con n   -> App (Con n)   elims'
          J       -> App J         elims'
          Refl    -> App Refl      elims'
          Meta mv -> App (Meta mv) elims'
      where
        elims' = map (>>>= f) elims

-- | Tries to apply the eliminators to the term.  Trows an error when
-- the term and the eliminators don't match.
eliminate :: Term v -> [Elim v] -> Term v
eliminate (App (Con _c) args) (Proj field : es) =
    if unField field >= length args
    then error $ "Term.eliminate: Bad elimination"
    else case (args !! unField field) of
           Apply t -> eliminate t es
           _       -> error $ "Term.eliminate: Bad constructor argument"
eliminate (Lam body) (Apply argument : es) =
    eliminate (instantiate1 argument body) es
eliminate (App h es1) es2 =
    App h (es1 ++ es2)
eliminate _ _ =
    error "Term.eliminate: Bad elimination"

-- Clauses
------------------------------------------------------------------------

-- | One clause of a function definition.
data Clause = Clause [Pattern] ClauseBody
    deriving (Eq, Ord)

type ClauseBody = Scope (Named Int) Term Void

data Pattern
    = VarP
    | ConP Name [Pattern]
    deriving (Eq, Ord)

-- Telescope
------------------------------------------------------------------------

-- | A 'Telescope' is a series of binding with some content at the end.
-- Each binding ranges over the rest of the telescope.
data Telescope t v
    = EmptyTel (t v)
    | t v :> Telescope (TermScope t) v
    deriving (Eq, Functor, Foldable, Traversable)

instance Bound Telescope where
    EmptyTel t  >>>= f = EmptyTel (t >>= f)
    (t :> tele) >>>= f = (t >>= f) :> (tele >>>= (Scope . return . F . f))

type ClosedTelescope t = Telescope t Void

-- Definition
------------------------------------------------------------------------

data Definition
    = Constant Name ConstantKind ClosedType
    | Constructor Name Name (ClosedTelescope Type)
    -- ^ Constructor name, data type name, parameter telescope.
    | Projection Name Field Name (ClosedTelescope Type)
    -- ^ Projection name, field number, record type name, parameter
    -- telescope.
    | Function Name ClosedType [Clause]

data ConstantKind = Postulate | Data | Record
  deriving Show

-- Context
------------------------------------------------------------------------

-- | A 'Context' is the same as a 'Telescope', but inside out: the last
-- binding we encounter ranges over all the precedent ones.
data Context v where
    EmptyContext :: Context Void
    (:<)         :: Context v -> (Name, Type v) -> Context (Var (Named ()) v)

contextLookup :: v -> Context v -> Type v
contextLookup v0 ctx0 = go ctx0 v0
  where
    -- Helper function so that we have the proof of equality when
    -- pattern matching the variable.
    go :: Context v -> v -> Type v
    go EmptyContext v = absurd v
    go (_ctx :< (_, type_)) (B _) = fmap F type_
    go ( ctx :< (_, _type)) (F v) = fmap F (go ctx v)

-- | Applies a 'Term' to all the variables in the context.
contextApp :: Term v -> Context v -> Term v
contextApp t ctx0 = eliminate t $ map (Apply . return) $ reverse $ go ctx0
  where
    go :: Context v -> [v]
    go EmptyContext           = []
    go (ctx :< (name, _type)) = B (named name ()) : map F (go ctx)

-- | Creates a 'Pi' type containing all the types in the 'Context' and
-- terminating with the provided 'Type'.
contextPi :: Context v -> Type v -> ClosedType
contextPi EmptyContext         t = t
contextPi (ctx :< (_n, type_)) t = contextPi ctx (Pi type_ (toScope t))
