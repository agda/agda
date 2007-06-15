------------------------------------------------------------------------
-- Small prelude
------------------------------------------------------------------------

module Prelude where

-- Basics.

open import Prelude.Function public
open import Prelude.Logic    public
open import Prelude.Product  public
open import Prelude.Sum      public

-- Binary relations.

open import Prelude.BinaryRelation                        public
open import Prelude.BinaryRelation.Conversion             public
open import Prelude.BinaryRelation.Product                public
open import Prelude.BinaryRelation.Sum                    public
open import Prelude.BinaryRelation.PropositionalEquality  public
open import Prelude.BinaryRelation.PropositionalEquality1 public
open import Prelude.BinaryRelation.OrderMorphism          public

-- Algebra.

import Prelude.Algebra
module Algebra = Prelude.Algebra
import Prelude.Algebra.RingProperties
module RingProperties = Prelude.Algebra.RingProperties
import Prelude.Algebra.LatticeProperties
module LatticeProperties = Prelude.Algebra.LatticeProperties
import Prelude.Algebra.Operations
module AlgebraOperations = Prelude.Algebra.Operations
open import Prelude.Algebraoid

-- Data.

open import Prelude.Bool            public
open import Prelude.Bool.Properties public
open import Prelude.Fin             public
open import Prelude.Maybe           public
open import Prelude.Nat             public
open import Prelude.Nat.Properties  public
open import Prelude.String          public
open import Prelude.Unit            public

import Prelude.List
import Prelude.Vec
module List = Prelude.List
module Vec  = Prelude.Vec

-- Utilities.

import Prelude.PreorderProof
module PreorderProof = Prelude.PreorderProof
