module README where

------------------------------------------------------------------------
-- The Agda "standard" library, version 0.2
--
-- Author: Nils Anders Danielsson, with contributions from
-- Jean-Philippe Bernardy, Samuel Bronson, Liang-Ting Chen, Dan Doel,
-- Patrik Jansson, Shin-Cheng Mu, and Ulf Norell
------------------------------------------------------------------------

-- This version of the library has been tested using Agda 2.2.4.

-- Note that no guarantees are currently made about forwards or
-- backwards compatibility, the library is still at an experimental
-- stage.

-- To make use of the library, add the path to the library’s root
-- directory (src) to the Agda search path, either using the
-- --include-path flag or by customising the Emacs mode variable
-- agda2-include-dirs (M-x customize-group RET agda2 RET).

-- To compile programs using some of the IO functions you need to
-- install the Haskell package utf8-string (available from Hackage).

-- Contributions to this library are welcome. Please send
-- contributions in the form of darcs patches (run
-- darcs send --output <patch file> and attach the patch file to an
-- email), and include a statement saying that you agree to release
-- your library patches under the library's licence.

------------------------------------------------------------------------
-- Module hierarchy
------------------------------------------------------------------------

-- The top-level module names of the library are currently allocated
-- as follows:
--
-- • Algebra
--     Abstract algebra (monoids, groups, rings etc.), along with
--     properties needed to specify these structures (associativity,
--     commutativity, etc.), and operations on and proofs about the
--     structures.
-- • Category
--     Category theory-inspired idioms used to structure functional
--     programs (functors and monads, for instance).
-- • Coinduction
--     Support for coinduction.
-- • Data
--     Data types and properties about data types. (Also some
--     combinators working solely on and with functions; see
--     Data.Function.)
-- • Foreign
--     Related to the foreign function interface.
-- • Induction
--     A general framework for induction (includes lexicographic and
--     well-founded induction).
-- • IO
--     Input/output-related functions.
-- • Relation
--     Properties of and proofs about relations (mostly homogeneous
--     binary relations).
-- • Size
--     Sizes used by the sized types mechanism.

------------------------------------------------------------------------
-- A selection of useful library modules
------------------------------------------------------------------------

-- Note that module names in source code are often hyperlinked to the
-- corresponding module. In the Emacs mode you can follow these
-- hyperlinks by typing M-. or clicking with the middle mouse button.

-- • Some data types

import Data.Bool     -- Booleans.
import Data.Char     -- Characters.
import Data.Empty    -- The empty type.
import Data.Fin      -- Finite sets.
import Data.List     -- Lists.
import Data.Maybe    -- The maybe type.
import Data.Nat      -- Natural numbers.
import Data.Product  -- Products.
import Data.Stream   -- Streams.
import Data.String   -- Strings.
import Data.Sum      -- Disjoint sums.
import Data.Unit     -- The unit type.
import Data.Vec      -- Fixed-length vectors.

-- • Some types used to structure computations

import Category.Functor      -- Functors.
import Category.Applicative  -- Applicative functors.
import Category.Monad        -- Monads.

-- • Equality

-- Propositional equality:
import Relation.Binary.PropositionalEquality

-- Convenient syntax for "equational reasoning" using a preorder:
import Relation.Binary.PreorderReasoning

-- Solver for commutative ring or semiring equalities:
import Algebra.RingSolver

-- • Properties of functions, sets and relations

-- Monoids, rings and similar algebraic structures:
import Algebra

-- Negation, decidability, and similar operations on sets:
import Relation.Nullary

-- Properties of homogeneous binary relations:
import Relation.Binary

-- • Induction

-- An abstraction of various forms of recursion/induction:
import Induction

-- Well-founded induction:
import Induction.WellFounded

-- Various forms of induction for natural numbers:
import Induction.Nat

-- • Support for coinduction

import Coinduction

-- • IO

import IO

------------------------------------------------------------------------
-- Record hierarchies
------------------------------------------------------------------------

-- When an abstract hierarchy of some sort (for instance semigroup →
-- monoid → group) is included in the library the basic approach is to
-- specify the properties of every concept in terms of a record
-- containing just properties, parameterised on the underlying
-- operations, sets etc.:
--
--   record IsSemigroup {A} (≈ : Rel A) (∙ : Op₂ A) : Set where
--     open FunctionProperties ≈
--     field
--       isEquivalence : IsEquivalence ≈
--       assoc         : Associative ∙
--       ∙-pres-≈      : ∙ Preserves₂ ≈ ⟶ ≈ ⟶ ≈
--
-- More specific concepts are then specified in terms of the simpler
-- ones:
--
--     record IsMonoid {A} (≈ : Rel A) (∙ : Op₂ A) (ε : A) : Set where
--       open FunctionProperties ≈
--       field
--         isSemigroup : IsSemigroup ≈ ∙
--         identity    : Identity ε ∙
--
--     open IsSemigroup isSemigroup public
--
-- Note here that open IsSemigroup isSemigroup public ensures that the
-- fields of the isSemigroup record can be accessed directly; this
-- technique enables the user of an IsMonoid record to use underlying
-- records without having to manually open an entire record hierarchy.
-- This is not always possible, though. Consider the following definition
-- of preorders:
--
--   record IsPreorder {A : Set}
--                     (_≈_ : Rel A) -- The underlying equality.
--                     (_∼_ : Rel A) -- The relation.
--                     : Set where
--     field
--       isEquivalence : IsEquivalence _≈_
--       -- Reflexivity is expressed in terms of an underlying equality:
--       reflexive     : _≈_ ⇒ _∼_
--       trans         : Transitive _∼_
--       ∼-resp-≈      : _∼_ Respects₂ _≈_
--
--     module Eq = IsEquivalence isEquivalence
--
--     refl : Reflexive _∼_
--     refl = reflexive Eq.refl
--
-- The Eq module in IsPreorder is not opened publicly, because it
-- contains some fields which clash with fields or other definitions
-- in IsPreorder.

-- Records packing up properties with the corresponding operations,
-- sets, etc. are sometimes also defined:
--
--   record Semigroup : Set₁ where
--     infixl 7 _∙_
--     infix  4 _≈_
--     field
--       carrier     : Set
--       _≈_         : Rel carrier
--       _∙_         : Op₂ carrier
--       isSemigroup : IsSemigroup _≈_ _∙_
--
--     open IsSemigroup isSemigroup public
--
--     setoid : Setoid
--     setoid = record { isEquivalence = isEquivalence }
--
--   record Monoid : Set₁ where
--     infixl 7 _∙_
--     infix  4 _≈_
--     field
--       carrier  : Set
--       _≈_      : Rel carrier
--       _∙_      : Op₂ carrier
--       ε        : carrier
--       isMonoid : IsMonoid _≈_ _∙_ ε
--
--     open IsMonoid isMonoid public
--
--     semigroup : Semigroup
--     semigroup = record { isSemigroup = isSemigroup }
--
--     open Semigroup semigroup public using (setoid)
--
-- Note that the Monoid record does not include a Semigroup field.
-- Instead the Monoid /module/ includes a "repackaging function"
-- semigroup which converts a Monoid to a Semigroup.

-- The above setup may seem a bit complicated, but we think it makes the
-- library quite easy to work with, while also providing enough
-- flexibility.

------------------------------------------------------------------------
-- More documentation
------------------------------------------------------------------------

-- Some examples showing where the natural numbers and some related
-- operations and properties are defined, and how they can be used:

import README.Nat

------------------------------------------------------------------------
-- Core modules
------------------------------------------------------------------------

-- Some modules have names ending in ".Core". These modules are
-- internal, and have (mostly) been created to avoid mutual recursion
-- between modules. They should not be imported directly; their
-- contents are reexported by other modules.

------------------------------------------------------------------------
-- All library modules
------------------------------------------------------------------------

-- For short descriptions of every library module, see Everything:

import Everything
