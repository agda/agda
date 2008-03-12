------------------------------------------------------------------------
-- Imports every non-internal module so that it is easy to see if
-- everything builds
------------------------------------------------------------------------

-- This module is also used to generate some overall documentation of
-- the library, by extracting the header of every module listed. Hence
-- internal modules should not be listed here. (Internal modules are
-- normally imported by other modules anyway.)

module Everything where

import Algebra
import Algebra.FunctionProperties
import Algebra.Morphism
import Algebra.Operations
import Algebra.Props.AbelianGroup
import Algebra.Props.BooleanAlgebra
import Algebra.Props.DistributiveLattice
import Algebra.Props.Group
import Algebra.Props.Lattice
import Algebra.Props.Ring
import Algebra.RingSolver
import Algebra.RingSolver.AlmostCommutativeRing
import Algebra.RingSolver.Lemmas
import Algebra.RingSolver.Simple
import Algebra.Structures

import Data.Bool
import Data.Bool.Properties
import Data.BoundedVec
import Data.BoundedVec.Inefficient
import Data.Char
import Data.DifferenceList
import Data.Fin
import Data.Fin.Dec
import Data.Fin.Props
import Data.Fin.Subset
import Data.Fin.Subset.Props
import Data.Function
import Data.HeterogeneousCollection
import Data.Integer
import Data.List
import Data.List.Properties
import Data.List1
import Data.Map
import Data.Maybe
import Data.Nat
import Data.Nat.Properties
import Data.Product
import Data.Product.Record
import Data.Sets
import Data.Star
import Data.Star.Fin
import Data.Star.List
import Data.Star.Lookup
import Data.Star.Nat
import Data.Star.Vec
import Data.String
import Data.Sum
import Data.Unit
import Data.Vec
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
import Relation.Binary.EqReasoning
import Relation.Binary.EqReasoning.Flexible
import Relation.Binary.FunctionLifting
import Relation.Binary.HeterogeneousEquality
import Relation.Binary.NonStrictToStrict
import Relation.Binary.OrderMorphism
import Relation.Binary.PartialOrderReasoning
import Relation.Binary.PartialOrderReasoning.Flexible
import Relation.Binary.PreorderReasoning
import Relation.Binary.PreorderReasoning.Flexible
import Relation.Binary.Product.NonStrictLex
import Relation.Binary.Product.Pointwise
import Relation.Binary.Product.StrictLex
import Relation.Binary.PropositionalEquality
import Relation.Binary.PropositionalEquality1
import Relation.Binary.Props.Poset
import Relation.Binary.Props.StrictPartialOrder
import Relation.Binary.Props.TotalOrder
import Relation.Binary.StrictToNonStrict
import Relation.Binary.Sum
import Relation.Nullary
import Relation.Nullary.Product
import Relation.Nullary.Sum
