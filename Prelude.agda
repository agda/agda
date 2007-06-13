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

open import Prelude.BinaryRelation                       public
open import Prelude.BinaryRelation.Conversion            public
open import Prelude.BinaryRelation.Product               public
open import Prelude.BinaryRelation.Sum                   public
open import Prelude.BinaryRelation.PropositionalEquality public
open import Prelude.BinaryRelation.OrderMorphism         public

-- Data.

open import Prelude.Bool   public
open import Prelude.Fin    public
open import Prelude.List   public
open import Prelude.Maybe  public
open import Prelude.Nat    public
open import Prelude.String public
open import Prelude.Unit   public
