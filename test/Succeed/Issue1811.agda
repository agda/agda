-- Andreas, 2016-02-02 postpone type checking of extended lambda
-- See also issue 480 and 1159

open import Common.Maybe
open import Common.String

record ⊤ : Set where

record IOInterface : Set₁ where
  field  Command   :  Set
         Response  :  (m : Command) → Set
open IOInterface

data IO I A : Set where
  do'      :  (c : Command I) (f : Response I c → IO I A)  → IO I A
  return   :  (a : A)                                      → IO I A

-- Alias of constructor which is a function
do :  ∀{I A} (c : Command I) (f : Response I c → IO I A) → IO I A
do c f    =  do' c f

data C : Set where
  getLine   :  C
  putStrLn  :  String → C

R : C → Set
R  getLine      =  Maybe String
R (putStrLn s)  =  ⊤

I : IOInterface
Command   I  =  C
Response  I  =  R

works : IO I ⊤
works = do'  getLine        λ{ nothing → return _ ; (just line) →
        do (putStrLn line)  λ _ →
        return _            }

test : IO I ⊤
test = do  getLine         λ{ nothing → return _ ; (just line) →
       do (putStrLn line)  λ _ →
       return _            }
