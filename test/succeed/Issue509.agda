-- Instance arguments in records.
module Issue509 where

-- The instance version of _
⋯ : {A : Set} {{ x : A }} → A
⋯ {{ x }} = x

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

record T (n : ℕ) : Set where
  field
    nextPrime : ℕ

T₁ : T (suc zero)
T₁ = record { nextPrime = suc (suc zero) }

T₂ : T (suc (suc zero))
T₂ = record { nextPrime = suc (suc (suc zero)) }

data Param : ℕ → Set where
  param : ∀ n → Param (suc n)

record R : Set where
  constructor r
  field
    {impl} : ℕ
    {{ inst }} : T impl
    p : Param impl
    s : ℕ

-- The inst field should be an instance meta here
testA : R
testA = record { p = param zero; s = suc (suc zero) }

-- So, pretty much this:
testB : R
testB = record { impl = _; inst = ⋯; p = param zero; s = suc (suc zero) }

-- Or using the construcor
testC : R
testC = r { _ } {{ ⋯ }} (param zero) (suc (suc zero))

-- Omitting the fields also works when using the constructor (of course)
testD : R
testD = r (param zero) (suc (suc zero))

-- Note that {{ _ }} means explicitly giving the instance argument and saying
-- it should be an ordinary meta. Going the other way would be {⋯}.
