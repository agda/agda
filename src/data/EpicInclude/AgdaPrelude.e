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

freadStr (stream : Ptr) -> Data =
    let isEof : Bool = foreign Int "feof" (stream : Ptr)
     in if isEof then Con 0 ()
                 else let str : String = %effect(foreign String "freadStrChunk" (stream : Ptr))
                       in Con 1 ( str , freadStr (stream))

readStr (u : Unit) -> Data =
    let isEof : Bool = foreign Int "eofstdin" ()
     in if isEof then Con 0 ()
                 else let str : String = %effect(foreign String "readStrChunk" ())
                       in Con 1 ( str , readStr (u))

primStringAppend (xs : Data, ys : Data) -> Data = case xs of
  { Con 0 ()                        -> ys
  | Con 1 (x : String, rest : Data) -> Con 1 (x, primStringAppend (rest, ys))
  }

length (xs : Data) -> Int = case xs of
  { Con 0 () -> 0
  | Con 1 (x : String, rest : Data) -> strlen(x) + length(rest)
  }

charAt (xs : Data, i : Int) -> Int = case xs of
  { Con 0 () -> error "index: out of bounds!"
  | Con 1 (x : String, rest : Data) -> 
    let len : Int = strlen(x)
     in (if i < len then foreign Int "strIndex" (x : String, i : Int)
                    else charAt (rest, i - len))
  }

mkString (xs : Data) -> String = case xs of
  { Con 0 () -> ""
  | Con 1 (s : String , rest : Data) -> 
    let rs : String = mkString (rest) in
    {-let rsLen : Int = strlen (rs) in
    if rsLen == 0 then s else-} foreign String "append" (s : String, rs : String)
  }

frString( xs : String) -> Data = Con 1 (xs , Con 0 ())

primStringEquality (xs : Data, ys : Data) -> Bool =
    foreign Int "eqString" (mkString(xs) : String, mkString(ys) : String)

charToString (c : Int) -> Data = 
    Con 1 (charToStr(c), Con 0 ())
charToStr (c : Int) -> String = 
    foreign String "charToStr" (c : Int)

strlen (s : String) -> Int = foreign Int "strlen" (s : String)

-- TODO: toList/fromList could be made slightly more efficient.

primStringToListS (xs : String) -> Data = %effect(
    let result : Data = primNil ()     in
    let i      : Int  = strlen (xs) - 1 in
    %while (i >= 0,
       let ! result = primCons (foreign Int "strIndex" (xs : String, i : Int), result) in
       let ! i      = i - 1 in
       unit) ;
    result)

primStringToList (xs : Data) -> Data = case xs of
  { Con 0 () -> primNil ()
  | Con 1 (str : String, rest : Data) -> primListAppend(primStringToListS(str), primStringToList(rest))
  }

map (f : Any, l : Any) -> Any = case l of
  { Con 0 () -> Con 0 ()
  | Con 1 (x : Any, xs : Any) -> Con 1 (f (x), map (f, xs))
  }

primStringFromList (l : Data) -> String = map (charToStr, l)


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

bigToStr (x:BigInt) -> Data =
    frString(foreign String "bigToStr" (x:BigInt))

strToBig (x : Data) -> Any = foreign BigInt "strToBig" (mkString(x) : String)

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



primZero() -> Any = foreign BigInt "bigZero" ()
primOne() -> Any  = foreign BigInt "bigOne" ()

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
