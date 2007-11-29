------------------------------------------------------------------------
-- Imports everything so that it is easy to see if everything builds
------------------------------------------------------------------------

module Everything where

import Algebra
import Algebra.Morphism
import Algebra.Operations
import Algebra.Packaged
import Algebra.Props.AbelianGroup
import Algebra.Props.AlmostCommRing
import Algebra.Props.BooleanAlgebra
import Algebra.Props.CommutativeRing
import Algebra.Props.CommutativeSemiring
import Algebra.Props.DistributiveLattice
import Algebra.Props.Group
import Algebra.Props.Lattice
import Algebra.Props.Ring
import Algebra.Props.Semiring
import Algebra.RingSolver
import Algebra.RingSolver.Examples
-- The following module is currently broken due to an Agda bug.
-- import Algebra.RingSolver.Int
import Algebra.RingSolver.Lemmas
import Algebra.RingSolver.Simple

import Data.Bool
import Data.Bool.Properties
import Data.BoundedVec
import Data.BoundedVec.Inefficient
import Data.Char
import Data.Fin
import Data.Fin.Dec
import Data.Fin.Props
import Data.Fin.Subset
import Data.Fin.Subset.Props
import Data.Function
import Data.HeterogeneousCollection
-- The following module is currently broken due to an Agda bug.
-- import Data.Int
import Data.Integer
import Data.List
import Data.List.Properties
import Data.Map
import Data.Maybe
import Data.Nat
import Data.Nat.Properties
import Data.Product
import Data.Product.Record
import Data.Sets
import Data.String
import Data.Sum
import Data.Unit
import Data.Vec
import Data.Vec.Core
import Data.Vec.Equality
import Data.Vec.Properties

import Logic
import Logic.Induction
import Logic.Induction.Lexicographic
import Logic.Induction.Nat

import Category.Applicative
import Category.Applicative.Indexed
import Category.Functor
import Category.Monad
import Category.Monad.Indexed
import Category.Monad.Identity
import Category.Monad.State

import Relation.Binary
import Relation.Binary.Consequences
import Relation.Binary.Consequences.Core
import Relation.Binary.Core
import Relation.Binary.EqReasoning
import Relation.Binary.FunctionLifting
import Relation.Binary.HeterogeneousEquality
import Relation.Binary.NonStrictToStrict
import Relation.Binary.OrderMorphism
import Relation.Binary.Product.NonStrictLex
import Relation.Binary.Product.PointWise
import Relation.Binary.Product.StrictLex
import Relation.Binary.PropositionalEquality
import Relation.Binary.PropositionalEquality.Core
import Relation.Binary.PropositionalEquality1
import Relation.Binary.Props.Poset
import Relation.Binary.Props.StrictPartialOrder
import Relation.Binary.Props.TotalOrder
import Relation.Binary.StrictToNonStrict
import Relation.Binary.Sum
import Relation.Nullary
import Relation.Nullary.Product
import Relation.Nullary.Sum
