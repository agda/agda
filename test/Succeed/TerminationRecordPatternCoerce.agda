-- 2010-10-05 Andreas

module TerminationRecordPatternCoerce where

data Empty : Set where

record Unit : Set where
  constructor unit

data Bool : Set where
  true false : Bool

T : Bool -> Set
T true = Unit
T false = Empty

data _==_ {A : Set}(a : A) : A -> Set where
  refl : a == a

subst : forall {A a b} -> a == b -> {P : A -> Set} -> P a -> P b
subst refl x = x

-- Thorsten suggests on the Agda list  thread "Coinductive families"
-- to encode lists as records
record List (A : Set) : Set where
  inductive
  constructor list
  field
    isCons : Bool
    head   : T isCons -> A
    tail   : T isCons -> List A

open List public

-- However, we have to be careful to preserve termination
-- in the presence of a lie

postulate
  lie : {b : Bool} -> T b

-- if the record constructor list was counted as structural increase
-- this function would not be rejected
f : {A : Set} -> (b : Bool) -> (l : List A) -> b == isCons l -> Unit
f .false (list false h t) refl = unit
f .true (list true h t) refl = f (isCons tl) tl refl
  where tl : List _
        tl = t unit
{- dot patterns inside of record patterns not supported!
f true (list .true h t) refl = f (isCons tl) tl refl
  where tl : List _
        tl = t unit
-}

-- however, it is almost like the following
f' : {A : Set} -> (b : Bool) -> (l : List A) -> b == isCons l -> Unit
f' false l p = unit
f' true (list b' h t) p = f' (isCons tl) tl refl
   where tl : List _
         tl = t (subst p {T} unit)

-- UPDATE: both of these are fine, since non-eta records patterns are not
-- translated to projections.
