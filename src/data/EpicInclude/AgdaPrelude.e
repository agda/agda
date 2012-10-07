%include "string.h"

-- IO

{-
%inline putStr (x:String) -> Unit =
    foreign Unit "wputStr" (x:String)

putStrLn (x:String) -> Unit =
    putStr(primStringAppend(x,"\n"))

readStr () -> String =
    foreign String "readStr" ()

intToStr (x:Int) -> String =
    foreign String "intToStr" (x:Int)

strToInt (x:String) -> Int =
    foreign String "strToInt" (x:String)

printInt (x:Int) -> Unit =
    foreign Unit "printInt" (x:Int)
-}

ioreturn (a : Any, u : Unit) -> Any = a
iobind (x : Any, f : Any, u : Unit) -> Any = %effect (let v : Any = %effect (x(u)) in f (v, u))

-- String operations

-- data String = Con 0 | Con 1 (Char*) String

freadStr (stream : Ptr) -> String =
    let isEof : Bool = foreign Int "feof" (stream : Ptr)
     in if isEof then Con 0 ()
                 else let str : String = %effect(foreign String "freadStrChunk" (stream : Ptr))
                       in primStringAppend( str , freadStr (stream))

readStr (u : Unit) -> String =
    let isEof : Bool = foreign Int "eofstdin" ()
     in if isEof then Con 0 ()
                 else let str : String = %effect(foreign String "readStrChunk" ())
                       in primStringAppend ( str , readStr (u))

primStringAppend (xs : String, ys : String) -> String = 
    foreign String "append" (xs : String, ys : String)


%inline length (xs : String) -> Int = strlen (xs)

charAt (xs : String, i : Int) -> Int = 
    foreign Int "strIndex" (xs : String , i : Int)

primStringEquality (xs : String, ys : String) -> Bool =
    foreign Int "eqString" (xs : String, ys : String)

charToString (c : Int) -> String  =
    foreign String "charToStr" (c : Int)

strlen (s : String) -> Int = foreign Int "strlen" (s : String)

-- TODO: toList/fromList could be made slightly more efficient.

primStringToList (xs : String) -> Data = %effect(
    let result : Data = primNil ()     in
    let i      : Int  = strlen (xs) - 1 in
    %while (i >= 0,
       let ! result = primCons (foreign Int "strIndex" (xs : String, i : Int), result) in
       let ! i      = i - 1 in
       unit) ;
    result)


map (f : Any, l : Any) -> Any = case l of
  { Con 0 () -> Con 0 ()
  | Con 1 (x : Any, xs : Any) -> Con 1 (f (x), map (f, xs))
  }

primStringFromList (l : Data) -> String = 
   case l of {
      Con 0 () -> ""
    | Con 1 (c : Char, cs : Data) -> strCons (c , primStringFromList(cs))
   }

strCons(i : Int , s : String) -> String =
   foreign String "strCons" (i : Int, s : String)

-- Lists

primNil () -> Data = Con 0 ()

primCons(x : Any , xs : Data) -> Data = Con 1 (x, xs)

listElim (op : Any, z : Any, xs : Data) -> Any = case xs of
  { Con 0 () -> z
  | Con 1 (y : Any, ys : Data) -> op (y, listElim(op, z, ys))
  }

primListAppend (xs : Data, ys : Data) -> Data = listElim(primCons, ys, xs)
-- Big number arithmetic

subBig (x:BigInt, y:BigInt) -> BigInt =
   foreign BigInt "subBig" (x:BigInt, y:BigInt)

gtBig (x:BigInt, y:BigInt) -> Bool =
   foreign Int "gtBig" (x:BigInt, y:BigInt)

leBig (x:BigInt, y:BigInt) -> Bool =
   foreign Int "leBig" (x:BigInt, y:BigInt)

geBig (x:BigInt, y:BigInt) -> Bool =
   foreign Int "geBig" (x:BigInt, y:BigInt)

printBig (x:BigInt) -> Unit =
   foreign Unit "printBig" (x:BigInt)

bigToStr (x:BigInt) -> String =
    foreign String "bigToStr" (x:BigInt)

strToBig (x : String) -> Any = foreign BigInt "strToBig" (x : String)

-- strToBig (x:String) -> Any =
--    foreign Any "strToBig" (x:String)

bigToInt (x : BigInt) -> Int =
    foreign Int "bigToInt" (x : BigInt)

-- Unit

%inline primUnit() -> Unit = unit

-- Nats

primNatPlus (x:Any, y:Any) -> Any =
   foreign Any "addBig" (x:Any, y:Any)

primNatTimes (x:Any, y:Any) -> Any =
   foreign Any "mulBig" (x:Any, y:Any)

%inline primNatMinus(x : Any, y : Any) -> Any = atLeastZeroBig(subBig(x, y))



primZero() -> Any = 0L -- foreign BigInt "bigZero" ()
primOne() -> Any  = 1L -- foreign BigInt "bigOne" ()

primSuc (n : Any) -> Any = primNatPlus(n, primOne())

primPred(n : Any) -> Any = subBig(n, primOne())

%inline atLeastZeroBig (x : Any) -> Any = 
  if primNatLess(x, primZero) 
     then primZero
     else x

primNatModSucAux(k : BigInt, m : BigInt, n : BigInt, j : BigInt) -> BigInt =
    foreign BigInt "modBig" (n : BigInt, m : BigInt)



primNatEquality (x:BigInt, y:BigInt) -> Bool =
    foreign Int "eqBig" (x:BigInt, y:BigInt)

primNatLess (x:BigInt, y:BigInt) -> Bool =
    foreign Int "ltBig" (x:BigInt, y:BigInt)


-- Bools

%inline primTrue  () -> Bool = true

%inline primFalse () -> Bool = false

-- Chars

printChar (x:Int) -> Unit =
    foreign Unit "printCharRep" (x:Int)

%inline primCharEquality (c1 : Int, c2 : Int) -> Bool = c1 == c2

primCharToNat (c : Int) -> BigInt = foreign BigInt "NEWBIGINTVALI" (c : Int)


-- Floats
floatToStr (x : Float) -> String =
    foreign String "floatToStr" (x : Float)

strToFloat (s : String) -> Float =
    foreign Float "strToFloat" (s : String)

-- Coinduction

primSharp (u1 : Any, u2 : Any, x : Any) -> Data = Con 0 (x)

-- RUNTIME

init () -> Unit =
    foreign Unit "init" ()
    
-- Levels

primLevelMax  (x : Any, y : Any) -> Any = 0L -- error "primLevelMax"
primLevelZero () -> Any = 0L -- error "primLevelZero"
primLevelSuc  (x : Any) -> Any = primSuc(x) -- error "primLevelSuc"

-- TrustMe

primTrustMe (a : Unit, x : Any, y : Any) -> Any = Con 0 ()
