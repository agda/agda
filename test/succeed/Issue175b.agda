
module Issue175b where

data _≡_ {A : Set}(x : A) : A → Set where
  refl : x ≡ x

data Bool : Set where
  true : Bool
  false : Bool
{-# BUILTIN BOOL Bool #-}
{-# BUILTIN TRUE true #-}
{-# BUILTIN FALSE false #-}

postulate ℝ : Set
{-# BUILTIN FLOAT ℝ #-}

primitive
  -- ℝ functions
  primFloatMinus : ℝ -> ℝ -> ℝ
  primFloatLess : ℝ -> ℝ -> Bool

_<_ : ℝ -> ℝ -> Bool
a < b = primFloatLess a b

data _≤_ : ℝ -> ℝ -> Set where
   ≤_ : {x y : ℝ} -> (x < y) ≡ true -> x ≤ y 
 
--absolute value
[|_|] : ℝ -> ℝ
[| a |] with (a < 0.0)
[| a |] | true = primFloatMinus 0.0 a
[| a |] | false = a

--error variable
ε : ℝ
ε = 1.0e-5

-- two floating point numbers can be said to be equal if their
-- difference is less than the given error variable
postulate
  reflℝ : {a b : ℝ} -> [| primFloatMinus a b |] ≤ ε -> a ≡ b

test : 1.0 ≡ 1.0000001
test =  reflℝ (≤ refl)
