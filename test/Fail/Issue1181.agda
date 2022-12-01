-- Check that let-bindings are preserved in error messages
module _ where

open import Agda.Builtin.Nat
open import Agda.Builtin.Sigma
open import Agda.Builtin.Equality

issue : Nat → Σ Nat λ m → Σ Nat λ n → Σ Nat λ p → m ≡ n * p
issue 0 = 0 , 0 , 0 , refl
issue (suc n) =
  let (a , b , c , d) = issue n
  in d

-- Should complain that
--  a ≡ b * c !=< Σ Nat ...
-- not
--  issue n .fst ≡ issue n .snd .fst * issue n .snd .snd .fst !=< Σ Nat ...
