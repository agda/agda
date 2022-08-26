module Agda.TypeChecking.Monad.Boundary where

import Control.DeepSeq
import Data.Data

import {-# SOURCE #-} Agda.TypeChecking.Pretty
import Agda.TypeChecking.Substitute.Class
import Agda.Syntax.Internal (Term, QName)


data BoundaryConstraint' term

newtype Boundary' term
  = Boundary { boundaryFaces :: [BoundaryConstraint' term] }

type BoundaryConstraint = BoundaryConstraint' Term
type Boundary = Boundary' Term

instance NFData t => NFData (Boundary' t)
instance Functor Boundary'
instance Foldable Boundary'
instance Traversable Boundary'

instance NFData t => NFData (BoundaryConstraint' t)
instance PrettyTCM t => PrettyTCM (BoundaryConstraint' t)
instance Functor BoundaryConstraint'
instance Foldable BoundaryConstraint'
instance Traversable BoundaryConstraint'
