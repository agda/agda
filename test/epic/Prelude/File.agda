{- An adaptation of Edwin Brady and Kevin Hammond's paper Scrapping your inefficient engine ... -}
{-# OPTIONS --type-in-type #-}
module File where

open import Bool
open import Bot
open import IO
open import Fin
open import Eq
open import Nat
open import Product
open import String
open import Unit
open import Vec

data Ty : Set where
  TyUnit   : Ty
  TyBool   : Ty
  TyLift   : Set -> Ty
  TyHandle : Nat -> Ty

interpTy : Ty -> Set
interpTy TyUnit       = Unit
interpTy TyBool       = Bool
interpTy (TyLift A)   = A
interpTy (TyHandle n) = Fin n

data Purpose : Set where
  Reading : Purpose
  Writing : Purpose
  
getMode : Purpose -> String
getMode Reading = "r"
getMode Writing = "w"

data FileState : Set where
  Open   : Purpose -> FileState
  Closed : FileState

postulate
  EpicFile : Set

FileVec : Nat -> Set
FileVec n = Vec FileState n

data FileHandle : FileState -> Set where
  OpenFile   : ∀{p} -> EpicFile -> FileHandle (Open p)
  ClosedFile : FileHandle Closed

data Env : ∀{n} -> FileVec n -> Set where
  Empty  : Env []
  Extend : {n : Nat}{T : FileState}{G : FileVec n} -> (res : FileHandle T) -> Env G -> Env (T :: G)

addEnd : ∀{n T}{G : FileVec n} -> Env G -> FileHandle T -> Env (snoc G T)
addEnd Empty         fh = Extend fh Empty
addEnd (Extend x xs) fh = Extend x (addEnd xs fh)

updateEnv : ∀{n T}{G : FileVec n} -> Env G -> (i : Fin n) -> (fh : FileHandle T) -> Env (G [ i ]= T)
updateEnv (Extend x xs) fz     e = Extend e xs
updateEnv (Extend x xs) (fs n) e = Extend x (updateEnv xs n e)
updateEnv Empty         ()     e

bound : ∀{n : Nat} -> Fin (S n)
bound {Z}   = fz
bound {S n} = fs (bound {n})


data OpenH : ∀{n} -> Fin n -> Purpose -> FileVec n -> Set where
  nil : ∀{p n}{as : FileVec n} -> OpenH fz p (Open p :: as)
  suc : ∀{p n a}{as : FileVec n}{i : Fin n} -> OpenH i p as -> OpenH (fs i) p (a :: as)

getFile : ∀{n}{i : Fin n}{p : Purpose}{ts : FileVec n} -> OpenH i p ts -> Env ts -> EpicFile
getFile nil (Extend (OpenFile f) env) = f
getFile (suc p)  (Extend _ env)             = getFile p env

getPurpose : {n : Nat} -> Fin n -> FileVec n -> Purpose
getPurpose f ts with ts ! f
... | Open p = p
... | Closed = Reading -- Should not happen right?

FilePath : Set
FilePath = String

data File : ∀{n n'}  -> FileVec n -> FileVec n' -> Ty -> Set where
  ACTION  : ∀{a l}{ts : FileVec l}  -> IO (interpTy a) -> File ts ts a
  RETURN  : ∀{a l}{ts : FileVec l}  -> interpTy a -> File ts ts a
  WHILE   : ∀{l}{ts : FileVec l}    -> File ts ts TyBool -> File ts ts TyUnit -> File ts ts TyUnit
  IF      : ∀{a l}{ts : FileVec l}  -> Bool -> File ts ts a -> File ts ts a -> File ts ts a
  BIND    : ∀{a b l l' l''}{ts : FileVec l}{ts' : FileVec l'}{ts'' : FileVec l''}
         -> File ts ts' a -> (interpTy a -> File ts' ts'' b) -> File ts ts'' b
  OPEN    : ∀{l}{ts : FileVec l}  
          -> (p : Purpose) -> (fd : FilePath) -> File ts (snoc ts (Open p)) (TyHandle (S l))
  CLOSE   : ∀ {l}{ts : FileVec l} -> (i : Fin l) -> (OpenH i (getPurpose i ts) ts) -> File ts (ts [ i ]= Closed) TyUnit
  GETLINE : ∀ {l}{ts : FileVec l} -> (i : Fin l) -> (p : OpenH i Reading ts) -> File ts ts (TyLift String)
  EOF     : ∀ {l}{ts : FileVec l} -> (i : Fin l) -> (p : OpenH i Reading ts) -> File ts ts TyBool
  PUTLINE : ∀ {l}{ts : FileVec l} -> (i : Fin l) -> (str : String) -> (p : OpenH i Writing ts) -> File ts ts TyUnit

postulate
  while  : IO Bool -> IO Unit -> IO Unit
  fopen  : FilePath -> String -> IO EpicFile
  fclose : EpicFile -> IO Unit
  fread  : EpicFile -> IO String
  feof   : EpicFile -> IO Bool
  fwrite : EpicFile -> String -> IO Unit 

{-# COMPILED_EPIC while (add : Any, body : Any, u : Unit) -> Any = %while (add(u), body(u)) #-}
{-# COMPILED_EPIC fopen (fp : String, mode : String, u : Unit) -> Ptr = foreign Ptr "fopen" (fp : String, mode : String) #-}
{-# COMPILED_EPIC fclose (file : Ptr, u : Unit) -> Unit = foreign Int "fclose" (file : Ptr); unit #-}
{-# COMPILED_EPIC fread (file : Ptr, u : Unit) -> Any = foreign Any "freadStr" (file : Ptr) #-}
{-# COMPILED_EPIC feof (file : Ptr, u : Unit) -> Bool = foreign Int "feof" (file : Ptr) #-}
{-# COMPILED_EPIC fwrite (file : Ptr, str : String, u : Unit) -> Unit =  foreign Unit "fputStr" (file : Ptr, str : String) #-}

fmap : {A B : Set} -> (A -> B) -> IO A -> IO B
fmap f io = 
  x <- io ,
  return (f x)

interp : ∀{n n' T}{ts : FileVec n}{ts' : FileVec n'} -> Env ts -> File ts ts' T -> IO (Env ts' × interpTy T)
interp env (ACTION io) = fmap (_,_ env) io
interp env (RETURN val) = return (env , val)
interp env (WHILE add body) =
    while (fmap snd (interp env add)) (fmap snd (interp env body)) ,,
    return (env , unit)
interp env (IF b t f) = if b then interp env t else interp env f
interp env (BIND code k) =
    v <- interp env code ,
    interp (fst v) (k (snd v))
interp env (OPEN p fpath) =
    fh <- fopen fpath (getMode p),
    return (addEnd env (OpenFile fh), bound)
interp env (CLOSE i p) = 
    fclose (getFile p env) ,,
    return (updateEnv env i ClosedFile , unit) 
interp env (GETLINE i p) = 
    fmap (_,_ env) (fread (getFile p env))
interp env (EOF i p) =
    e <- feof (getFile p env) ,
    return (env , e)
interp env (PUTLINE i str p) =
    fmap (_,_ env) (fwrite (getFile p env) str ,, fwrite (getFile p env) "\n")

printBool : Bool -> IO Unit
printBool b = putStr (if b then "true" else "false")

allClosed : (n : Nat) -> FileVec n
allClosed Z     = []
allClosed (S n) = Closed :: allClosed n

cat : File [] (Closed :: []) TyUnit
cat = BIND (OPEN Reading "hej")
            cont
 where
  cont : Fin 1 -> File (Open Reading :: []) (Closed :: []) TyUnit
  cont (fs ())
  cont fz =  BIND (WHILE (BIND (EOF fz nil) (\b -> RETURN (not b))) 
                         (BIND (GETLINE fz nil) 
                               (\str -> ACTION (putStrLn str))
                         )
                  )
                  (λ x → CLOSE fz nil)

main : IO Unit
main = fmap snd (interp Empty cat)
