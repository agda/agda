{-# OPTIONS_GHC -Wunused-imports #-}

module Agda.TypeChecking.MetaVars where

import Agda.Syntax.Common           ( Arg )
import Agda.Syntax.Internal         ( MetaId, Term, Type, Args, Dom, Abs, Telescope, Sort, Substitution )
import Agda.TypeChecking.Monad.Base ( TCM, RunMetaOccursCheck, Comparison, CompareAs, CompareDirection, MetaVariable )
import Agda.TypeChecking.Monad.MetaVars (MonadMetaSolver)
import Data.IntMap (IntMap)

instance MonadMetaSolver TCM

type Condition = Dom Type -> Abs Type -> Bool
type SubstCand = [(Int,Term)]

newArgsMeta'      :: Condition -> Type -> TCM Args
newArgsMeta       :: Type -> TCM Args
assignTerm        :: MetaId -> [Arg String] -> Term -> TCM ()
assign            :: CompareDirection -> MetaId -> Args -> Term -> CompareAs -> TCM ()
newInstanceMeta   :: String -> Type -> TCM (MetaId, Term)
newValueMeta      :: RunMetaOccursCheck -> Comparison -> Type -> TCM (MetaId, Term)
newNamedValueMeta :: RunMetaOccursCheck -> String -> Comparison -> Type -> TCM (MetaId, Term)
newNamedValueMeta':: RunMetaOccursCheck -> String -> Comparison -> Type -> TCM (MetaId, Term)
newTelMeta        :: Telescope -> TCM Args
newSortMeta       :: TCM Sort
checkMetaInst     :: MetaId -> TCM ()
isFaceConstraint  :: MetaId -> Args -> TCM (Maybe (MetaVariable, IntMap Bool, SubstCand, Substitution))
