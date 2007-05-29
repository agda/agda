module Q where
import AlonzoPrelude
open AlonzoPrelude -- , using(Bool,False,True,String,showBool)
import PreludeNat
open PreludeNat
import PreludeBool
open PreludeBool
import PreludeShow
open PreludeShow



pred : Nat -> Nat
pred (zero) = zero
pred (suc n) = n

mplus : Nat -> Nat -> Nat
mplus zero y = y
mplus (suc n) y = suc (mplus n  y ) 

Q : Bool -> Set
Q true = Nat	
Q false = Bool

f : (b : Bool) -> Q b
f true = pred 3
f false = true

mid : {A : Set} -> A -> A 
mid x = x 

mainS : String
mainS = showBool (f (const false true))
