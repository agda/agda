-- Andreas, 2017-01-26.
-- The --no-eta-equality option

{-# OPTIONS --no-eta-equality #-}
{-# OPTIONS --allow-unsolved-metas #-}

-- is only valid for the record types defined in this file.

open import HaveEtaForImportedRecords.EtaRecord

-- Eta holds for the imported record.

test-imported : ∀{x y : ⊤} → x ≡ y
test-imported = refl

-- Eta does not hold for a record defined here

record Unit : Set where

test : Unit
test = _   -- Should be yellow!
