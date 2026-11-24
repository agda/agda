open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _==_)
open import Agda.Builtin.Reflection using (Name; primQNameToWord64s)
open import Agda.Builtin.Sigma using (Σ; fst; snd)
open import Agda.Builtin.Word using (Word64; primWord64ToNat)
open import Common.Bool using (if_then_else_)
open import Common.IO using (IO; _>>=_; putStrLn)
open import Common.String using (String; _+S+_; primShowNat)
open import Common.Unit using (Unit)
open import Agda.Builtin.Unit using (⊤)

words : Name → Σ Word64 (λ _ → Word64)
words = primQNameToWord64s

nameHash : Name → Nat
nameHash name = primWord64ToNat (snd (words name))

_ : nameHash (quote Nat) ≡ 13537827747504913145
_ = refl

_ : nameHash (quote Word64) ≡ 8673354731180355553
_ = refl

render : Name → String
render name = primShowNat (primWord64ToNat (fst (words name))) +S+ " " +S+
              primShowNat (nameHash name)

main : IO Unit
main = putStrLn (render (quote Nat)) >>= λ _ →
       putStrLn (render (quote Word64)) >>= λ _ →
       putStrLn (if nameHash (quote Nat) == nameHash (quote ⊤)
                 then "same module hashes" else "different module hashes")
