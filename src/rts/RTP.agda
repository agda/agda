module RTP where
  open import RTN public

{-
  data Bool : Set where
    False : Bool
    True : Bool
-}


  postulate
    Int    : Set
    String : Set
    Float  : Set
    Char   : Set

  {-# BUILTIN FLOAT Float #-}
  {-# BUILTIN STRING String #-}
  {-# BUILTIN CHAR Char #-}

  -- postulate primShowBool : Bool -> String
  postulate primShowInt : Int -> String
  postulate primShowChar : Char -> String
  
  postulate primStringAppend : String -> String -> String
  postulate primStringReverse : String -> String

  -- postulate primStringToList : String -> List Char
  -- postulate primStringFromList 


-- Int stuff
  postulate primIntZero : Int
  postulate primIntOne : Int
  postulate primIntSucc : Int -> Int
  postulate primNatToInt : Nat -> Int
  postulate primIntToNat : Int -> Nat
  postulate primIntAdd : Int -> Int -> Int
  postulate primIntSub : Int -> Int -> Int
  postulate primIntMul : Int -> Int -> Int
  postulate primIntDiv : Int -> Int -> Int
  postulate primIntMod : Int -> Int -> Int
