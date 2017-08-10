postulate
  A : Set

data B (a : A) : Set where
  conB : B a → B a → B a

data C (a : A) : B a → Set where
  conC : {bl br : B a} → C a bl → C a br → C a (conB bl br)

-- Second bug, likely same as first bug.
{-
An internal error has occurred. Please report this as a bug.
Location of the error: src/full/Agda/TypeChecking/Abstract.hs:133
-}
data F : Set where
  conF : F

boo : (a : A) (b : B a) (c : C a _) → Set
boo a b (conC tl tr) with tr | conF
... | _ | _ = _
