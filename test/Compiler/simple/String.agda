module String where

open import Common.IO
open import Common.List
open import Common.String
open import Common.Unit


testString : String
testString = "To boldly go where no man gone before"

printList : {A : Set} -> (A -> IO Unit) -> List A -> IO Unit
printList p [] = return unit
printList p (x ∷ xs) =
    p x ,,
    printList p xs

main : IO Unit
main =
    putStrLn testString ,,
    printList printChar (stringToList testString) ,,
    putStrLn "" ,,
    putStrLn (fromList (stringToList testString)) ,,
    putStrLn (primShowString testString) ,,
    return unit
