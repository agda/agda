
module Lib.Monad where

open import Lib.Nat
open import Lib.List
open import Lib.IO hiding (IO; mapM)
open import Lib.Maybe
open import Lib.Prelude

infixr 40 _>>=_ _>>_
infixl 90 _<*>_ _<$>_

-- Wrapper type, used to ensure that ElM is constructor-headed.

record IO (A : Set) : Set where
  constructor io
  field unIO : Lib.IO.IO A

open IO

-- State monad transformer

data StateT (S : Set)(M : Set -> Set)(A : Set) : Set where
  stateT : (S -> M (A × S)) -> StateT S M A

runStateT : forall {S M A} -> StateT S M A -> S -> M (A × S)
runStateT (stateT f) = f

-- Reader monad transformer

data ReaderT (E : Set)(M : Set -> Set)(A : Set) : Set where
  readerT : (E -> M A) -> ReaderT E M A

runReaderT : forall {E M A} -> ReaderT E M A -> E -> M A
runReaderT (readerT f) = f

-- The monad class

data Monad : Set1 where
  maybe  : Monad
  list   : Monad
  io     : Monad
  state  : Set -> Monad -> Monad
  reader : Set -> Monad -> Monad

ElM : Monad -> Set -> Set
ElM maybe        = Maybe
ElM list         = List
ElM io           = IO
ElM (state S m)  = StateT S (ElM m)
ElM (reader E m) = ReaderT E (ElM m)

return : {m : Monad}{A : Set} -> A -> ElM m A
return {maybe}      x = just x
return {list}       x = x :: []
return {io}         x = io (returnIO x)
return {state _ m}  x = stateT \s -> return (x , s)
return {reader _ m} x = readerT \_ -> return x

_>>=_ : {m : Monad}{A B : Set} -> ElM m A -> (A -> ElM m B) -> ElM m B
_>>=_ {maybe}     nothing    k = nothing
_>>=_ {maybe}     (just x)   k = k x
_>>=_ {list}      xs         k = foldr (\x ys -> k x ++ ys) [] xs
_>>=_ {io}        (io m)     k = io (bindIO m (unIO ∘ k))
_>>=_ {state S m} (stateT f) k = stateT \s -> f s >>= rest
  where
    rest : _ × _ -> ElM m _
    rest (x , s) = runStateT (k x) s
_>>=_ {reader E m} (readerT f) k = readerT \e -> f e >>= \x -> runReaderT (k x) e

-- State monad class

data StateMonad (S : Set) : Set1 where
  state : Monad -> StateMonad S
  reader : Set -> StateMonad S -> StateMonad S

ElStM : {S : Set} -> StateMonad S -> Monad
ElStM {S} (state m)    = state S m
ElStM     (reader E m) = reader E (ElStM m)

ElSt : {S : Set} -> StateMonad S -> Set -> Set
ElSt m = ElM (ElStM m)

get : {S : Set}{m : StateMonad S} -> ElSt m S
get {m = state m}    = stateT \s -> return (s , s)
get {m = reader E m} = readerT \_ -> get

put : {S : Set}{m : StateMonad S} -> S -> ElSt m Unit
put {m = state m}    s = stateT  \_ -> return (unit , s)
put {m = reader E m} s = readerT \_ -> put s

-- Reader monad class

data ReaderMonad (E : Set) : Set1 where
  reader : Monad -> ReaderMonad E
  state  : Set -> ReaderMonad E -> ReaderMonad E

ElRdM : {E : Set} -> ReaderMonad E -> Monad
ElRdM {E} (reader m)  = reader E m
ElRdM     (state S m) = state S (ElRdM m)

ElRd : {E : Set} -> ReaderMonad E -> Set -> Set
ElRd m = ElM (ElRdM m)

ask : {E : Set}{m : ReaderMonad E} -> ElRd m E
ask {m = reader m } = readerT \e -> return e
ask {m = state S m} = stateT \s -> ask >>= \e -> return (e , s)

local : {E A : Set}{m : ReaderMonad E} -> (E -> E) -> ElRd m A -> ElRd m A
local {m = reader _ } f (readerT m) = readerT \e -> m (f e)
local {m = state S _} f (stateT m)  = stateT \s -> local f (m s)

-- Derived functions

-- Monad operations

_>>_ : {m : Monad}{A B : Set} -> ElM m A -> ElM m B -> ElM m B
m₁ >> m₂ = m₁ >>= \_ -> m₂

_<*>_ : {m : Monad}{A B : Set} -> ElM m (A -> B) -> ElM m A -> ElM m B
mf <*> mx = mf >>= \f -> mx >>= \x -> return (f x)

_<$>_ : {m : Monad}{A B : Set} -> (A -> B) -> ElM m A -> ElM m B
f <$> m = return f <*> m

mapM : {m : Monad}{A B : Set} -> (A -> ElM m B) -> List A -> ElM m (List B)
mapM f []        = return []
mapM f (x :: xs) = _::_ <$> f x <*> mapM f xs

-- State monad operations

modify : {S : Set}{m : StateMonad S} -> (S -> S) -> ElSt m Unit
modify f = get >>= \s -> put (f s)


-- Test

-- foo : Nat -> Maybe (Nat × Nat)
-- foo s = runReaderT (runStateT m s) s
--  where

-- m₁ : StateT Nat (ReaderT Nat Maybe) Nat
-- m₁ = local suc (ask >>= \s -> put (s + 3) >> get)

-- The problem: nested injective function don't seem to work
-- as well as one could hope. In this case:
--   ElM (ElRd ?0) == ReaderT Nat Maybe
-- inverts to
--    ElRd ?0 == reader Nat ?1
--    ElM ?1 == Maybe
-- it seems that the injectivity of ElRd isn't taken into account(?)
-- m : ReaderT Nat Maybe Nat
-- m = ask

