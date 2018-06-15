-- Andreas, 2016-02-02 postpone type checking of extended lambda
-- See also issue 480 and 1159

open import Common.Maybe
open import Common.String

record ⊤ : Set where

record IOInterface : Set₁ where
  field  Command   :  Set
         Response  :  (m : Command) → Set
open IOInterface

data IO I (A : Set) : Set where
  act'     :  (c : Command I) (f : Response I c → IO I A)  → IO I A
  return   :  (a : A)                                      → IO I A

-- Alias of constructor which is a function
act :  ∀{I A} (c : Command I) (f : Response I c → IO I A) → IO I A
act c f    =  act' c f

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
works = act'  getLine        λ{ nothing → return _ ; (just line) →
        act (putStrLn line)  λ _ →
        return _            }

test : IO I ⊤
test = act  getLine         λ{ nothing → return _ ; (just line) →
       act (putStrLn line)  λ _ →
       return _            }

-- Test with do-notation

_>>=_ : ∀ {A B} → IO I A → (A → IO I B) → IO I B
act' c f >>= k = act' c λ x → f x >>= k
return a >>= k = k a

_>>_ : ∀ {A B} → IO I A → IO I B → IO I B
m >> m' = m >>= λ _ → m'

getLineIO : IO I (Maybe String)
getLineIO = act' getLine return

putStrLnIO : String → IO I ⊤
putStrLnIO s = act' (putStrLn s) return

works' : IO I ⊤
works' = do
  just line ← getLineIO where nothing → return _
  putStrLnIO line
  return _
