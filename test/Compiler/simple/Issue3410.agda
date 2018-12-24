
open import Common.IO
open import Agda.Builtin.String
open import Agda.Builtin.Unit
open import Agda.Builtin.Nat
open import Agda.Builtin.Sigma
open import Agda.Builtin.Equality
open import Agda.Builtin.Bool
open import Agda.Builtin.Strict

data ∋⋆ : Set where
  Z : ∋⋆

data ⊢⋆ : Set where
  size⋆ : Nat → ⊢⋆

⋆Sub : Set
⋆Sub = ∋⋆ → ⊢⋆

data TermCon : ⊢⋆ → Set where
  integer : (s : Nat) → TermCon (size⋆ s)

data ⊢_ : ⊢⋆ → Set where
  con : ∀ {s} → TermCon (size⋆ s) → ⊢ size⋆ s

data Value : {A : ⊢⋆} → ⊢ A → Set where
  V-con : ∀ {n} → (cn : TermCon (size⋆ n)) → Value (con cn)

notErased : Nat → Bool
notErased n = primForce n λ _ → true

BUILTIN : (σ : ⋆Sub) (vtel : Σ (⊢ σ Z) Value) → Bool
BUILTIN σ vtel with σ Z
BUILTIN σ (_ , V-con (integer s)) | _ = notErased s
-- Either of these work:
-- BUILTIN σ (_ , V-con (integer s)) | size⋆ s = notErased s
-- BUILTIN σ (con (integer s) , V-con (integer s)) | _ = notErased s

con2 : ⊢ size⋆ 8
con2 = con (integer 8)

vcon2 : Value con2
vcon2 = V-con (integer 8)

builtin2plus2 : Bool
builtin2plus2 = BUILTIN (λ _ → size⋆ 8) (con2 , vcon2)

help : Bool → String
help true  = "4"
help false = "something went wrong"

check : "4" ≡ help builtin2plus2
check = refl

main : IO ⊤
main = putStrLn (help builtin2plus2)
