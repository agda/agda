module Conv where

import Val

data G a = Success a | Fail String

instance  Monad G  where
    (Success x) >>= k     =  k x
    Fail s   >>= k   =  Fail s
    return           =  Success
    fail             =  Fail

gensym :: Int -> Name -> Val -> G Val
gensym n s u = return (mvar (Gen n s u))

eq :: Int -> Val -> Val -> Val -> G ()       -- u1 = u2 : A; int is there for creating fresh values
eqT :: Int -> Val -> Val -> G ()             -- A1 = A2; int is there for creating fresh values
eqs :: Int -> Val -> [Val] -> [Val] -> G ()  -- equality of vector of values

eqT _ Set Set = return ()
eqT n (Fun a1 f1) (Fun a2 f2) =
 do
   eqT n a1 a2
   u <- gensym n "X" a1
   eqT (n+1) (f1 u) (f2 u)
eqT n u1 u2 = eq n Set u1 u2

eq n (Fun a f) u1 u2 =
 do
   u <- gensym n "X" a
   eq (n+1) (f u) (app u1 u) (app u2 u)
eq n _ (App h1 us1) (App h2 us2) =
 if eqH h1 h2 then eqs n (typH h1) us1 us2
      else fail ("eq1 " ++ showVal (App h1 us1) ++ "=/=" ++ showVal (App h2 us2))
eq _ _ u1 u2 = fail ("eq2 " ++ showVal u1 ++ " =/= " ++ showVal u2)

eqs n (Fun a f) (u1:us1) (u2:us2) =
 do
  eq n a u1 u2
  eqs n (f u1) us1 us2
eqs _ _ [] [] = return ()
eqs _ _ _ _ = fail "eqs"

showVal (Lam _) = "Lam"
showVal (App h vs) = showH h ++ " " ++ showVals vs
showVal Set = "Set"
showVal (Fun v _) = "Fun " ++ showVal v

showVals [] = ""
showVals (v:vs) = showVal v ++ " ," ++ showVals vs

showH (Gen _ n _) = n
showH (Const n _) = n
showH (Prim n _) = n
