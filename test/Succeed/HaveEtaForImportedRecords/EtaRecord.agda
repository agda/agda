-- Andreas, 2017-01-26.  Testing the --no-eta-equality option.

-- Records in files without the option (unless Agda runs with this
-- option globally), should have eta.

module HaveEtaForImportedRecords.EtaRecord where

open import Agda.Builtin.Equality public

record ⊤ : Set where

private
  test : ∀{x y : ⊤} → x ≡ y
  test = refl
