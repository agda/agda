{-# LANGUAGE DeriveFunctor  #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE GADTs #-}
module Impl.Term
    ( -- * Base 'Term'
      TermScope
    , TermVar
    , boundTermVar
    , Term(..)
    , Type
    , ClosedTerm
    , ClosedType
    , TermElim
    , eliminate
      -- * 'view' and 'unview'
    , TermView
    , view
    , unview
    ) where

import Prelude hiding (pi, abs)

import           Bound
import           Prelude.Extras                   (Eq1)
import           Data.Foldable                    (Foldable)
import           Data.Traversable                 (Traversable)
import           Data.Void                        (Void)

import           Syntax.Abstract                  (Name)
import           Term
import qualified Term.View                        as TV

-- Base terms
------------------------------------------------------------------------

-- | Something abstracting over 1 term.
type TermScope = Scope (Named ())

-- | A 'Var' with one 'Named' free variable.
type TermVar = Var (Named ())

boundTermVar :: Name -> TermVar v
boundTermVar n = B $ named n ()

-- | Base term type.
data Term v
    = Lam (TermScope Term v)
    | Pi (Term v) (TermScope Term v)
    | Equal (Term v) (Term v) (Term v)
    | App (Head v) [TermElim v]
    | Set
    deriving (Eq, Functor, Foldable, Traversable)

instance Eq1 Term

-- | A 'Type' is a 'Term', but the synonym helps documenting.
type Type = Term

-- | A 'Term' with no free variables.
type ClosedTerm = Term Void
type ClosedType = Type Void

type TermElim = Elim Term

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
eliminate :: Term v -> [TermElim v] -> Term v
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

-- View
-------

type TermView = TV.Term TermScope Term

view :: Term v -> TermView v
view (Lam abs)            = TV.Lam abs
view (Pi domain codomain) = TV.Pi domain codomain
view (Equal type_ x y)    = TV.Equal type_ x y
view (App h els)          = TV.App h els
view Set                  = TV.Set

unview :: TermView v -> Term v
unview = undefined
