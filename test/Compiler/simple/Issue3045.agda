-- cj-xu and fredriknordvallforsberg, 2018-04-30

open import Common.IO

data Bool : Set where
  true false : Bool

data MyUnit : Set where
  tt : MyUnit -- no eta!

HiddenFunType : MyUnit -> Set
HiddenFunType tt = Bool -> Bool

notTooManyArgs : (x : MyUnit) -> HiddenFunType x
notTooManyArgs tt b = b

{- This should not happen when compiling notTooManyArgs:

    • Couldn't match expected type ‘GHC.Prim.Any’
                  with actual type ‘a0 -> b0’
      The type variables ‘b0’, ‘a0’ are ambiguous
    • The equation(s) for ‘d10’ have two arguments,
      but its type ‘T2 -> AgdaAny’ has only one
-}

main : IO MyUnit
main = return tt
