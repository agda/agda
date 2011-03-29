-- {-# OPTIONS --verbose tc.records.ifs:15 #-}
-- {-# OPTIONS --verbose tc.rec.proj:15 #-}
-- {-# OPTIONS --verbose tc.rec:15 #-}
-- {-# OPTIONS --verbose tc.constr.findInScope:15 #-}
-- {-# OPTIONS --verbose tc.term.args.ifs:15 #-}
-- {-# OPTIONS --verbose tc.section.apply:15 #-}
-- {-# OPTIONS --verbose tc.mod.apply:15 #-}

module 02-classes-indep where

import Data.Empty as E

data T : Set where
  tt : T

data Bool : Set where
  true : Bool
  false : Bool

module testMod (a : Bool) where
  testModEntry : Bool
  testModEntry = a

record Monoid (t : Set) : Set where
  field
    zeroT : t
    plusT : t → t → t
  test : Bool
  test = false
  --module test {a : Bool} = testMod a
  

--module WI {t : Set} {{r : Monoid t}} = Monoid r

or : Bool → Bool → Bool
or true _ = true
or _ true = true
or false false = false

aT : Monoid T
aT = record { zeroT = tt; plusT = λ _ _ → tt }

-- testMonoid : {t : Set} → {{tM : Monoid t}} → t → t
-- testMonoid {{tM}} t = let open Monoid tM in plusT t zeroT

aBool : Monoid Bool
aBool = record { zeroT = false; plusT = or }

-- test : Bool
-- test = testMonoid false

-- imp : {a : Bool} → Bool
-- imp {b} = b

-- imp' : {a : Bool} → Bool
-- -- imp' = imp 
-- -- imp' = λ {a} → imp {a}
-- imp' {a} = imp {a}

--test2 : {t : Set} → {{tM : Monoid t}} → t
--test2 {t} {{tM}} = Monoid.WithImplicits.zeroT {t} 

open MonoidWithImplicits

test3 : T
test3 = zeroT 

-- test4 : {{bM : Monoid Bool}} → Bool
-- test4 {{bM}} = Monoid.WithImplicits.zeroT 

⋯ : {A : Set} → {{v : A}} → A
⋯ {{v}} = v

test5 : Bool
test5 = Monoid.zeroT ⋯
