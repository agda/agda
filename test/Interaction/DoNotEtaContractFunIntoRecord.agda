-- Andreas, 2013-09-17
module DoNotEtaContractFunIntoRecord where

record _×_ (A B : Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B

postulate
  A : Set
  B : Set
  P : (B → A × B) → Set

goal : (x : A) → P (λ y → x , y)
goal x = {!!}

-- Goal should be displayed as
--   P (λ y → x , y)
-- rather than as
--   P (_,_ x)
