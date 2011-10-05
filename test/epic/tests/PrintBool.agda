module tests.PrintBool where

open import Prelude.IO
open import Prelude.Bool
open import Prelude.Char
open import Prelude.List
open import Prelude.Unit
open import Prelude.String

isNewline : Char -> Bool
isNewline '\n' = true
isNewline _    = false

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


main : IO Unit
main = 
    printChar 'a' ,,
    printList ('a' :: 'b' :: 'c' :: []) ,,
    putStrLn "printBool" ,,
    printBool (isNewline '\n') ,,
    printBool (isNewline 'a') ,,
    return unit