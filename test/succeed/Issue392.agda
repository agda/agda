-- Andreas, 2011-09-11
module Issue392 where

import Common.Irrelevance  

-- Create an irrelevant record R1 (all fields irrelevant).
record R1 : Set1 where
  field
    .f1 : Set

{- module R1 .(r : R1) where
     .f1 : Set -- = R1.f1 r    
-}

-- Create an irrelevant instance f2 of R1.
record R2 : Set2 where
  field
    .f2 : R1
    f3  : Set
  
-- This succeeds even though f2 is irrelevant.
  open R1 f2 public

{- A more realistic use would be s.th. like

  record IsEquivalence {a ℓ} {A : Set a}
                       (_≈_ : Rel A ℓ) : Set (a ⊔ ℓ) where
    field
      .refl  : Reflexive _≈_
      .sym   : Symmetric _≈_
      .trans : Transitive _≈_

  record Setoid c ℓ : Set (suc (c ⊔ ℓ)) where
    infix 4 _≈_
    field
      Carrier       : Set c
      _≈_           : Rel Carrier ℓ
      .isEquivalence : IsEquivalence _≈_

    open IsEquivalence isEquivalence public
-}
