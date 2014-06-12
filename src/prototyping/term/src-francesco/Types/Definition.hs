{-# LANGUAGE OverloadedStrings #-}
module Types.Definition
    ( -- * 'Clause'
      Clause(..)
    , ClauseBody
    , Pattern(..)
      -- * 'Definition'
    , Definition(..)
    , ConstantKind(..)
    , TermHead(..)
    , InjectiveClauses(..)
    , ignoreInjective
    , mapInjective
    ) where

import           Bound
import           Data.Typeable                    (Typeable)
import           Control.Arrow                    (second)

import           Syntax.Abstract                  (Name)
import qualified Types.Telescope                  as Tel
import           Types.Term
import           Types.Var
import qualified Text.PrettyPrint.Extended        as PP
import           Text.PrettyPrint.Extended        ((<+>), ($$))

-- Clauses
------------------------------------------------------------------------

type ClauseBody t v = Scope (Named Int) t v

-- | One clause of a function definition.
data Clause t v = Clause [Pattern] (ClauseBody t v)
    deriving (Eq, Typeable)

instance Bound Clause where
  Clause pats body >>>= f = Clause pats (body >>>= f)

data Pattern
    = VarP
    | ConP Name [Pattern]
    deriving (Eq, Show)

instance PP.Pretty Pattern where
  prettyPrec p e = case e of
    VarP      -> PP.text "_"
    ConP c es -> PP.prettyApp p (PP.pretty c) es

-- Definition
------------------------------------------------------------------------

data Definition t v
    = Constant ConstantKind (t v)
    | Constructor Name (Tel.IdTel t v)
    -- ^ Data type name, parameter context with resulting type.
    | Projection Field Name (Tel.IdTel t v)
    -- ^ Field number, record type name, parameter context with resulting type.
    | Function (t v) (InjectiveClauses t v)
    deriving (Typeable)

instance Bound Definition where
  Constant kind t              >>>= f = Constant kind (t >>= f)
  Constructor tyCon type_      >>>= f = Constructor tyCon (type_ >>>= f)
  Projection field tyCon type_ >>>= f = Projection field tyCon (type_ >>>= f)
  Function type_ clauses       >>>= f = Function (type_ >>= f) (mapInjective (>>>= f) clauses)

data ConstantKind
    = Postulate
    | Data [Name]                 -- Constructor list
    | Record Name [(Name, Field)] -- Constructor and projection list
  deriving (Eq, Show, Typeable)

data InjectiveClauses t v
    = NotInjective [Clause t v]
    | Injective [(TermHead, Clause t v)]

deriving instance (IsTerm t) => Show (Closed (InjectiveClauses t))

data TermHead = PiHead | DefHead Name
    deriving (Eq, Show)

ignoreInjective :: InjectiveClauses t v -> [Clause t v]
ignoreInjective (NotInjective clauses) = clauses
ignoreInjective (Injective injClauses) = map snd injClauses

mapInjective :: (Clause t v -> Clause t' v')
             -> InjectiveClauses t v -> InjectiveClauses t' v'
mapInjective f (NotInjective clauses) = NotInjective $ map f clauses
mapInjective f (Injective injClauses) = Injective $ map (second f) injClauses

-- Pretty printing
------------------------------------------------------------------------

instance (IsTerm t) => PP.Pretty (Closed (Definition t)) where
  pretty (Constant Postulate type_) =
    prettyView type_
  pretty (Constant (Data dataCons) type_) =
    "data" <+> prettyView type_ <+> "where" $$
    PP.nest 2 (PP.vcat (map PP.pretty dataCons))
  pretty (Constant (Record dataCon fields) type_) =
    "record" <+> prettyView type_ <+> "where" $$
    PP.nest 2 ("constructor" <+> PP.pretty dataCon) $$
    PP.nest 2 ("field" $$ PP.nest 2 (PP.vcat (map (PP.pretty . fst) fields)))
  pretty (Constructor tyCon type_) =
    "constructor" <+> PP.pretty tyCon $$ PP.nest 2 (prettyTele type_)
  pretty (Projection _ tyCon type_) =
    "projection" <+> PP.pretty tyCon $$ PP.nest 2 (prettyTele type_)
  pretty (Function type_ clauses) =
    prettyView type_ $$
    PP.vcat (map PP.pretty (ignoreInjective clauses))

prettyTele :: (IsVar v, IsTerm t) => Tel.IdTel t v -> PP.Doc
prettyTele (Tel.Empty (Tel.Id t)) =
   prettyView t
prettyTele (Tel.Cons (n0, type0) tel0) =
  "[" <+> PP.pretty n0 <+> ":" <+> prettyView type0 PP.<> go tel0
  where
    go :: (IsVar v, IsTerm t) => Tel.IdTel t v -> PP.Doc
    go (Tel.Empty (Tel.Id t)) =
      "]" <+> prettyView t
    go (Tel.Cons (n, type_) tel) =
      ";" <+> PP.pretty n <+> ":" <+> prettyView type_ <+> prettyTele tel

instance (IsTerm t) => Show (Closed (Definition t)) where
  show = PP.render . PP.pretty

instance PP.Pretty ConstantKind where
  pretty = PP.text . show

instance (IsTerm t) => PP.Pretty (Closed (Clause t)) where
  pretty (Clause pats body) =
    PP.pretty pats <+> "=" $$ PP.nest 2 (prettyView (fromScope body))

instance (IsTerm t) => Show (Closed (Clause t)) where
  show = PP.render . PP.pretty
