module PrintBool where

open import Common.IO
open import Common.Bool
open import Common.Char
open import Common.List
open import Common.Unit
open import Common.String

isNewline : Char -> Bool
isNewline '\n' = true
isNewline _    = false

sequence : {A : Set} -> List (IO A) -> IO (List A)
sequence [] = return []
sequence (x ∷ xs) =
    r <- x ,
    rs <- sequence xs ,
    return (r ∷ rs)

mapM : {A B : Set} -> (A -> IO B) -> List A -> IO (List B)
mapM f xs = sequence (map f xs)

printList : List Char -> IO Unit
printList xs =
  mapM printChar xs ,,
  printChar '\n'


main : IO Unit
main =
    printChar 'a' ,,
    printList ('a' ∷ 'b' ∷ 'c' ∷ []) ,,
    putStrLn "printBool" ,,
    printBool (isNewline '\n') ,,
    printBool (isNewline 'a') ,,
    return unit
