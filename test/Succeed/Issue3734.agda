-- Andreas, 2020-06-21, issue #3734, reported 2019-05-01 by gallais
-- User warnings also on constructors and pattern synonyms.

-- {-# OPTIONS -v scope.warning.usage:50 #-}

data A : Set where
  s : A → A
  a : A

b : A
b = a  -- (usage of a, but no warning yet installed)

{-# WARNING_ON_USAGE a "Used a" #-}

_ : A
_ = a  -- usage of a

_ : A → A
_ = λ where
  a →  -- pattern usage of a
    a  -- usage of a
  x → x

_ : A
_ = s b  -- (usage of a via b, need not show)

pattern c = s a  -- usage of a

{-# WARNING_ON_USAGE c "Used c" #-}

_ : A
_ = c  -- usage of c

_ : A → A
_ = λ where
  c →     -- pattern usage of c
    a     -- usage of a
  x → x

-- Ambiguous constructors

module M where
  data D1 : Set where cons : D1
  {-# WARNING_ON_USAGE cons "Warning on D1.cons (shouldn't show)" #-}

data D2 : Set where cons : D2
{-# WARNING_ON_USAGE cons "Warning on D2.cons (should show)" #-}

open M

d2 : D2
d2 = cons  -- usage of D2.cons

f2 : D2 → Set
f2 cons = A  -- pattern usage of D2.cons


-- Ambiguous attachments of warnings shall apply to all disambiguations.

data Amb1 : Set where amb : Amb1
data Amb2 : Set where amb : Amb2

{-# WARNING_ON_USAGE amb "Ambiguous constructor amb was used" #-}

test1 : Amb1
test1 = amb

test2 : Amb2
test2 = amb
