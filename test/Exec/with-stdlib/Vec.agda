-- Written by P. Hausmann
module Vec where

open import IO
open import Data.Vec
open import Data.Nat
open import Data.Nat.Show

Matrix : Set -> ℕ -> ℕ -> Set
Matrix a n m = Vec (Vec a m) n

madd : {n m : ℕ} -> Matrix ℕ m n -> Matrix ℕ m n -> Matrix ℕ m n
madd a b = map (λ x → \y -> map _+_ x ⊛ y) a ⊛ b

idMatrix : {n : ℕ} -> Matrix ℕ n n
idMatrix {zero} = []
idMatrix {suc n} = (1 ∷ (replicate zero)) ∷ (map (λ x → zero ∷ x) idMatrix)

transpose : {n m : ℕ} {a : Set} -> Matrix a m n -> Matrix a n m
transpose {zero} {zero} a₁ = []
transpose {zero} {suc m} {a} x = []
transpose {suc n} {zero} a₁ = replicate []
transpose {suc n} {suc m} {a} (_∷_ x₁ x₂) with map head (x₁ ∷ x₂)
... | vm = vm ∷ (map _∷_ (tail x₁) ⊛ transpose (map tail x₂))

-- We use quite small numbers right now, as with big number the computation
-- gets very slow (at least in MAlonzo)
-- correct result : 109
compute : ℕ
compute = sum (map sum g)
  where m : Matrix ℕ 3 3
        m = (3 ∷ 5 ∷ 9 ∷ []) ∷
              (12 ∷ 0 ∷ 7 ∷ []) ∷ (11 ∷ 2 ∷ 4 ∷ []) ∷ []
        g : Matrix ℕ 3 3
        g = madd (transpose (transpose m)) (transpose (madd m idMatrix))

main = run (putStrLn (show compute))
