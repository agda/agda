{-# OPTIONS --allow-unsolved-metas #-}
-- {-# OPTIONS -v tc.conv.elim:100 #-}
module Issue814 where

record IsMonoid (M : Set) : Set where
  field
    unit : M
    _*_ : M → M → M

record Monoid : Set₁ where
  field
    carrier : Set
    is-mon : IsMonoid carrier

record Structure (Struct : Set₁)
                 (HasStruct : Set → Set)
                 (carrier : Struct → Set) : Set₁ where
  field
    has-struct : (X : Struct) → HasStruct (carrier X)

mon-mon-struct : Structure Monoid IsMonoid Monoid.carrier
mon-mon-struct = record
  { has-struct = Monoid.is-mon }

mon-mon-struct' : Structure Monoid IsMonoid Monoid.carrier
mon-mon-struct' = record
  { has-struct = Monoid.is-mon }

unit : {Struct : Set₁}{C : Struct → Set}
     → ⦃ X : Struct ⦄
     → ⦃ struct : Structure Struct IsMonoid C ⦄
     → C X
unit {Struct}{C} ⦃ X ⦄ ⦃ struct ⦄ = IsMonoid.unit (Structure.has-struct struct X)

f : (M : Monoid) → Monoid.carrier M
f M = unit

-- An internal error has occurred. Please report this as a bug.
-- Location of the error: src/full/Agda/TypeChecking/Eliminators.hs:45

-- This used to crash, but should only produce unsolved metas.
