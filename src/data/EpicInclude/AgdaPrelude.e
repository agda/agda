%include "string.h"

-- IO

%inline putStr (x:String) -> Unit =
    foreign Unit "putStr" (x:String)

putStrLn (x:String) -> Unit =
    putStr(append(x,"\n"))

readStr () -> String =
    foreign String "readStr" ()

intToStr (x:Int) -> String =
    foreign String "intToStr" (x:Int)

strToInt (x:String) -> Int =
    foreign String "strToInt" (x:String)

printInt (x:Int) -> Unit =
    foreign Unit "printInt" (x:Int)

ioreturn (a : Any, u : Unit) -> Any = a
iobind (x : Any, f : Any, u : Unit) -> Any = f (x (u), u)

-- String operations

append (x:String, y:String) -> String =
    foreign String "append" (x:String, y:String)

length (x:String) -> String =
    foreign Int "strlen" (x:String)

index (x:String, i:Int) -> Char =
    foreign Int "strIndex" (x:String, i:Int)

-- Big number arithmetic

subBig (x:BigInt, y:BigInt) -> BigInt =
   foreign BigInt "subBigInt" (x:BigInt, y:BigInt)

gtBig (x:BigInt, y:BigInt) -> Bool =
   foreign Int "gtBigInt" (x:BigInt, y:BigInt)

leBig (x:BigInt, y:BigInt) -> Bool =
   foreign Int "leBigInt" (x:BigInt, y:BigInt)

geBig (x:BigInt, y:BigInt) -> Bool =
   foreign Int "geBigInt" (x:BigInt, y:BigInt)

printBig (x:BigInt) -> Unit =
   foreign Unit "printBigInt" (x:BigInt)

bigIntToStr (x:BigInt) -> String =
    foreign String "bigIntToStr" (x:BigInt)

strToBigInt (x:String) -> Int =
    foreign String "strToBigInt" (x:String)

-- Unit

%inline primUnit() -> Unit = unit

-- Nats

primNatPlus (x:BigInt, y:BigInt) -> BigInt =
   foreign BigInt "addBigInt" (x:BigInt, y:BigInt)

primNatTimes (x:BigInt, y:BigInt) -> BigInt =
   foreign BigInt "mulBigInt" (x:BigInt, y:BigInt)

primZero() -> BigInt = 0L

primSuc (n : BigInt) -> BigInt = primNatPlus(n, 1L)

primPred(n : BigInt) -> BigInt = subBig(n, 1L)

%inline absBig (x : BigInt) -> BigInt = 
  if primNatLess(x, primZero) 
     then primZero
     else x

%inline primNatMinus(x : BigInt, y : BigInt) -> BigInt = absBig(subBig(x, y))

-- readInt () -> Int = foreign Int "readInt" ()

primNatEquality (x:BigInt, y:BigInt) -> Bool =
    foreign Int "eqBigInt" (x:BigInt, y:BigInt)

primNatLess (x:BigInt, y:BigInt) -> Bool =
    foreign Int "ltBigInt" (x:BigInt, y:BigInt)

-- Strings

-- Cannot call foreign "append" directly, for some reason
%inline primStringAppend (x : String, y : String) -> String = append(x, y)

primStringEquality (x : String, y : String) -> Bool =
    foreign Int "eqString" (x : String, y : String)

-- Bools

%inline primTrue  () -> Bool = true

%inline primFalse () -> Bool = false

-- Chars

printChar (x:Int) -> Unit =
    foreign Unit "printCharRep" (x:Int)

init () -> Unit =
    foreign Unit "init" ()

-- Coinduction

primSharp (u1 : Any, u2 : Any, x : Any) -> Data = Con 0 (x)