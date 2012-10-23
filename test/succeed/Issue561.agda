
module Issue561 where

open import Common.Prelude

open import Common.MAlonzo
  -- if I do not include this, I get compilation errors
  -- MAlonzo/Code/Common/Prelude.hs:8:7:
  --   Not in scope: type constructor or class `Common.FFI.Nat'



primitive
  primIsDigit : Char → Bool

postulate
  return : ∀ {A} → A → IO A

main : IO Bool
main = return true
