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

Q : Bool -> Set
Q true = Nat	
Q false = Bool

f : (b : Bool) -> Q b
f true = pred 3
f false = true

mainS : String
mainS = showBool (f (const false true))
