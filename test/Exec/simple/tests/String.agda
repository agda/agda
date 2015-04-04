module tests.String where

open import Prelude.IO
open import Prelude.List
open import Prelude.String
open import Prelude.Unit


testString : String
testString = "To boldly go where no man gone before"

printList : forall {A} -> (A -> IO Unit) -> List A -> IO Unit
printList p [] = return unit
printList p (x :: xs) =
    p x ,,
    printList p xs

main : IO Unit
main =
    putStrLn testString ,,
    printList printChar (fromString testString) ,,
    putStrLn "" ,,
    putStrLn (fromList (fromString testString)) ,,
    return unit
