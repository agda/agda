-- An Agda implementation of the n queens program from the nofib
-- benchmark. Very inefficient, uses unary natural numbers instead of
-- machine integers.

module N-queens where

open import Category.Monad
open import Coinduction
open import Data.Bool hiding (_≟_)
open import Data.Char hiding (_≟_)
open import Data.Fin using (#_)
open import Data.Digit
open import Data.Integer as Z using (+_; _⊖_)
open import Data.List as List
open import Data.Maybe as Maybe
open import Data.Nat
open import Data.Nat.Show
open import Data.String as String using (String)
open import Data.Unit hiding (_≟_)
open import Function
open import IO using (IO)
import IO.Primitive as Primitive
open import Relation.Nullary.Decidable

------------------------------------------------------------------------
-- Things missing from the standard library

take_[_…] : ℕ → ℕ → List ℕ
take zero  [ n …] = []
take suc k [ n …] = n ∷ take k [ suc n …]

[_…_] : ℕ → ℕ → List ℕ
[ m              … n              ] with compare m n
[ .(suc (n + k)) … n              ] | greater .n k = []
[ m              … .m             ] | equal .m     = [ m ]
[ m              … .(suc (m + k)) ] | less .m k    = take (2 + k) [ m …]

guard : Bool → List ⊤
guard true  = [ _ ]
guard false = []

postulate
  getArgs′ : Primitive.IO (List String)

{-# IMPORT System.Environment #-}
{-# COMPILED getArgs′ System.Environment.getArgs #-}

getArgs : IO (List String)
getArgs = lift getArgs′
  where open IO

read : List Char → Maybe ℕ
read [] = nothing
read ds = fromDigits ∘ reverse <$> mapM Maybe.monad charToDigit ds
  where
  open RawMonad Maybe.monad

  charToDigit : Char → Maybe (Digit 10)
  charToDigit '0' = just (# 0)
  charToDigit '1' = just (# 1)
  charToDigit '2' = just (# 2)
  charToDigit '3' = just (# 3)
  charToDigit '4' = just (# 4)
  charToDigit '5' = just (# 5)
  charToDigit '6' = just (# 6)
  charToDigit '7' = just (# 7)
  charToDigit '8' = just (# 8)
  charToDigit '9' = just (# 9)
  charToDigit _   = nothing

------------------------------------------------------------------------
-- The main program

nsoln : ℕ → ℕ
nsoln nq = length (gen nq)
  where
  open RawMonad List.monad

  safe : ℕ → ℕ → List ℕ → Bool
  safe x d []      = true
  safe x d (q ∷ l) = not ⌊ x ≟ q ⌋ ∧
                     not ⌊ x ≟ q + d ⌋ ∧
                     not ⌊ + x Z.≟ q ⊖ d ⌋ ∧
                     -- Equivalent to previous line, because x ≥ 1:
                     -- not ⌊ x ≟ q ∸ d ⌋ ∧
                     safe x (1 + d) l

  gen : ℕ → List (List ℕ)
  gen zero    = [ [] ]
  gen (suc n) =
    gen n              >>= λ b →
    [ 1 … nq ]         >>= λ q →
    guard (safe q 1 b) >>
    return (q ∷ b)

main = run (♯ getArgs >>= λ arg → ♯ main′ arg)
  where
  open IO

  main′ : List String → IO ⊤
  main′ (arg ∷ []) with read (String.toList arg)
  ... | just n  = putStrLn (show (nsoln n))
  ... | nothing = return _
  main′ _ = return _
