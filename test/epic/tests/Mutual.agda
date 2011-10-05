module tests.Mutual where

open import Prelude.IO
open import Prelude.String
open import Prelude.Unit

mutual
  data G : Set where
    GA : {g : G}(f : F g) -> G
    GB : G

  data F : G -> Set where
    FA : (g : G) -> F g
    FB : F GB

mutual
  incG : G -> G
  incG GB     = GA FB
  incG (GA f) = GA (incF f)

  incF : {g : G} -> F g -> F (incG g)
  incF FB     = FA (GA FB)
  incF (FA g) = FA (incG g)
  



mutual
  PrintF : {g : G} -> F g -> String
  PrintF FB = "FB"
  PrintF (FA g) = "(FA " +S+ PrintG g +S+ ")"
  
  PrintG : G -> String
  PrintG GB     = "GB"
  PrintG (GA f) = "(GA " +S+ PrintF f +S+ ")"
  
main : IO Unit
main =
    putStrLn (PrintF (FA (GA (FA GB)))) ,,
    putStrLn (PrintG (incG (GA (incF FB)))) ,, -- 
    return unit