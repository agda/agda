{-# OPTIONS --no-termination-check #-}
module RunTests where

open import Prelude.Bool
open import Prelude.Char
open import Prelude.Nat
open import Prelude.List
open import Prelude.IO
open import Prelude.String
open import Prelude.Unit
open import Prelude.Product

postulate
  Stream : Set
  popen  : String -> String -> IO Stream
  pclose : Stream -> IO Unit
  readChar : Stream -> IO Char
  strLen : String -> Nat
  charAt : (s : String) -> Nat -> Char
  
_`_`_ : {A B C : Set}(x : A)(f : A -> B -> C)(y : B) -> C
x ` f ` y = f x y 

infixr 9 _∘_

_∘_ : {A : Set}{B : A -> Set}{C : (x : A) -> B x -> Set}
      (f : {a : A}(b : B a)-> C a b)
      (g : (a : A) -> B a)(x : A) -> C x (g x)
f ∘ g = λ x -> f (g x) 

infixr 1 _$_

_$_ : {A : Set}{B : A -> Set}(f : (x : A) -> B x)(x : A) -> B x
f $ x = f x

{-# COMPILED_EPIC popen (s : String, m : String, u : Unit) -> Ptr = foreign Ptr "popen" (s : String, m : String) #-}
{-# COMPILED_EPIC pclose (s : Ptr, u : Unit) -> Unit = foreign Int "pclose" (s : Ptr) ; u #-}
{-# COMPILED_EPIC readChar (s : Ptr, u : Unit) -> Int = foreign Int "fgetc" (s : Ptr) #-}
{-# COMPILED_EPIC strLen (s : Any) -> BigInt = foreign BigInt "intToBig" (foreign Int "strlen" (s : String) : Int) #-}
{-# COMPILED_EPIC charAt (s : Any, n : BigInt) -> Int = foreign Int "charAtBig" (s : String, n : BigInt) #-}

readStream : Stream -> IO (List Char)
readStream stream =
    c <- readChar stream ,
    if' charEq eof c 
        then pclose stream ,, return [] 
        else ( cs <- readStream stream 
             , return (c :: cs))

system : String -> IO (List Char)
system s = 
    putStrLn $ "system " +S+ s ,,
    x <- popen s "r" ,
    y <- readStream x ,
    return y

span : {A : Set} -> (p : A -> Bool) -> List A -> List A × List A
span p [] = [] , []
span p (a :: as) with p a
... | false = [] , a :: as
... | true with span p as
...        | xs , ys = (a :: xs) , ys

groupBy : {A : Set} -> (A -> A -> Bool) -> List A -> List (List A)
groupBy _  []           = []
groupBy eq (x :: xs) with span (eq x) xs
... | ys , zs = (x :: ys) :: groupBy eq zs

comparing : {A B : Set} -> (A -> B) -> (B -> B -> Bool) -> A -> A -> Bool
comparing f _==_ x y = f x == f y

FilePath : Set
FilePath = String

and : List Bool -> Bool
and [] = true
and (true :: xs) = and xs
and (false :: _) = false

sequence : {A : Set} -> List (IO A) -> IO (List A)
sequence [] = return []
sequence (x :: xs) =
    r <- x ,
    rs <- sequence xs ,
    return (r :: rs)

mapM : {A B : Set} -> (A -> IO B) -> List A -> IO (List B)
mapM f xs = sequence (map f xs)

printList : List Char -> IO Unit
printList xs = 
  mapM printChar xs ,,
  printChar '\n'

printResult : FilePath -> List Char -> List Char -> IO Unit
printResult filename l1 l2 with l1 ` listEq charEq ` l2 
... | true  = putStrLn (filename +S+ ": Success!")
... | false = putStrLn (filename +S+ ": Fail!") ,,
              putStrLn "Expected:" ,, 
              printList l2       ,,
              putStrLn "Got:"      ,,
              printList l1       

compile : FilePath -> FilePath -> IO Unit
compile dir file = 
    system $ "agda --epic --compile-dir=" +S+ dir +S+ "bin/ " +S+ dir +S+ file ,,
    return unit

readFile : FilePath -> IO (List Char)
readFile file = system $ "cat " +S+ file

-- This won't work because of a bug in Epic...

{-
validFile : List Char -> Bool
validFile f with span (not ∘ charEq '.') f
... | _ , ('.' :: 'a' :: 'g' :: 'd' :: 'a' :: []) = true
... | _ , ('.' :: 'o' :: 'u' :: 't' :: [])        = true
... | _                                           = false
-}

stripFileEnding : FilePath -> FilePath
stripFileEnding fp = fromList $ fst $ span (not ∘ charEq '.') (fromString fp)

testFile : FilePath -> FilePath -> FilePath -> IO Bool
testFile outdir agdafile outfile = 
    compile outdir (agdafile)           ,,
    out      <- system $ outdir +S+ "bin/" +S+ stripFileEnding agdafile ,
    expected <- readFile (outdir +S+ outfile)    ,
    printResult agdafile out expected ,,
    return (out ` listEq charEq ` expected)

testFile' : FilePath -> List (List Char) -> IO Bool
testFile' outdir (agdafile :: outfile :: _) = testFile outdir (fromList agdafile) (fromList outfile)
testFile' _      _                          = return true

isNewline : Char -> Bool
isNewline '\n' = true
isNewline _    = false

lines : List Char -> List (List Char)
lines list with span (not ∘ isNewline) list
... | l , [] = l :: []
... | l , _ :: s' = l :: lines s'

getFiles : FilePath -> IO (List (List Char))
getFiles dir =
    out <- system $ "ls " +S+ dir ,
    putStrLn "getFiles after ls" ,,
   -- mapM (printList ∘ snd) $ map (span (not ∘ charEq '.')) $ lines out ,,
    return $ lines out -- filter validFile $ lines out

isDot : Char -> Bool
isDot '.' = true
isDot _   = false

testFiles : FilePath -> IO Bool
testFiles dir = 
    files <- getFiles dir ,
    putStrLn "Found the following files in the tests directory:" ,,
    mapM printList files   ,,
    res   <- mapM (testFile' dir) (groupBy (comparing (fst ∘ span (not ∘ isDot)) (listEq charEq)) files) ,
    return $ and res

getCurrentDirectory : IO FilePath
getCurrentDirectory = 
   fromList <$> system "pwd" 

main : IO Unit
main =
    dir' <- getCurrentDirectory ,
    putStrLn (fromList (fromString dir')) ,,
    putStrLn "hello" ,,
    putStrLn (fromList (tail ('h' :: 'e' :: 'j' :: []))) ,,
    printList (fromString "hej igen") ,,
    putStrLn (fromList (tail (fromString "hello"))) ,,
    dir <- fromList ∘ init ∘ fromString <$> getCurrentDirectory ,
    putStrLn dir ,,
    system ("rm " +S+ dir +S+ "/tests/*.agdai") ,,
    res <- testFiles (dir +S+ "/tests/") ,
    (if res 
      then putStrLn "All tests succeeded! "
      else putStrLn "Not all tests succeeded ")
