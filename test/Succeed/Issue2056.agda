data Size : Set where

↑ : Size → Size
↑ ()

data N : Size → Set where
  suc : ∀{i} (a : N i) → N (↑ i)

data Val : ∀{i} (t : N i) → Set where
  val : ∀{i} (n : N i) → Val (suc n)

record R (j : Size) : Set where
  field num : N j

data W {j} (ft : R j) : Set where
  immed : (v : Val (R.num ft)) → W ft

postulate
  E : ∀{j} (ft : R j) (P : (w : W ft) → Set) → Set

test : ∀ {j} (ft : R j) → Set
test {j} ft = E {j} ft testw
  where
  testw : ∀ {ft : R _} (w : W ft) → Set
  testw (immed (val a)) = test record{ num = a }

-- testw passes without quantification over ft
-- or with _ := j

{- OLD ERROR

Cannot instantiate the metavariable _35 to solution ↑ i since it
contains the variable i which is not in scope of the metavariable
or irrelevant in the metavariable but relevant in the solution
when checking that the pattern val a has type Val (R.num ft₁)
-}
