module DeBruijnExSubst where

open import Prelude -- using (_∘_)       -- composition, identity
open import Data.Maybe
open import Logic.Identity renaming (subst to subst≡)
import Logic.ChainReasoning
module Chain = Logic.ChainReasoning.Poly.Homogenous _≡_ (\x -> refl) (\x y z -> trans)
open Chain

open import DeBruijn

-- untyped de Bruijn terms 
data LamE (A : Set) : Set where
    varE  : A -> LamE A
    appE  : LamE A -> LamE A -> LamE A
    absE  : LamE (Maybe A) -> LamE A
    flatE : LamE (LamE A) -> LamE A

-- functoriality of LamE 
lamE : {A B : Set} -> (A -> B) -> LamE A -> LamE B
lamE f (varE a)     = varE (f a)
lamE f (appE t1 t2) = appE (lamE f t1) (lamE f t2)
lamE f (absE r)     = absE (lamE (fmap f) r)
lamE f (flatE r)    = flatE (lamE (lamE f) r)

{- from TCS 05 paper
eval' : {A B : Set} -> (A -> B) -> LamE A -> Lam B
eval' f (varE a)     = var (f a)
eval' f (appE t1 t2) = app (eval' f t1) (eval' f t2)
eval' f (absE r)     = abs (eval' (fmap f) r) 
eval' f (flatE r)    = subst id (eval' (eval' f) r)

eval : {A : Set} -> LamE A -> Lam A
eval = eval' id
-}

eval : {A : Set} -> LamE A -> Lam A
eval (varE a)     = var a
eval (appE t1 t2) = app (eval t1) (eval t2)
eval (absE r)     = abs (eval r)
eval (flatE r)    = subst eval (eval r)

evalNAT : {A B : Set}(f : A -> B) -> (t : LamE A) -> 
  eval (lamE f t) ≡ lam f (eval t)
evalNAT f (varE a)     = refl
evalNAT f (appE t1 t2) =
  chain> eval (lamE f (appE t1 t2))
     === eval (appE (lamE f t1) (lamE f t2))
       by refl
     === app (eval (lamE f t1)) (eval (lamE f t2))
       by refl
     === app (lam f (eval t1))  (eval (lamE f t2))
       by cong (\ x -> app x (eval (lamE f t2))) (evalNAT f t1)
     === app (lam f (eval t1))  (lam f (eval t2))
       by cong (\ x -> app (lam f (eval t1)) x)  (evalNAT f t2)
     === lam f (app (eval t1) (eval t2))
       by refl
     === lam f (eval (appE t1 t2))
       by refl
evalNAT f (absE r) =
  chain> eval (lamE f (absE r))
     === eval (absE (lamE (fmap f) r))   by  refl
     === abs (eval (lamE (fmap f) r))    by  refl
     === abs (lam (fmap f) (eval r))     by  cong abs (evalNAT (fmap f) r)
     === lam f (abs (eval r))            by  refl
     === lam f (eval (absE r))           by  refl
evalNAT f (flatE r) = 
  chain> eval (lamE f (flatE r))
     === eval (flatE (lamE (lamE f) r))
       by refl
     === subst eval (eval (lamE (lamE f) r))
       by refl
     === subst eval (lam (lamE f) (eval r))
       by cong (subst eval) (evalNAT (lamE f) r)
     === subst (eval ∘ lamE f) (eval r)
       by substLaw1 (lamE f) eval (eval r)
     === subst (lam f ∘ eval) (eval r)
       by substExt _ _ (evalNAT f) (eval r)
     === lam f (subst eval (eval r))
       by substLaw2 f eval (eval r)
     === lam f (eval (flatE r))
       by refl

evalNATcor : {A : Set}(ee : LamE (LamE A)) ->
  subst id (eval (lamE eval ee)) ≡ eval (flatE ee)
evalNATcor ee = 
  chain> subst id (eval (lamE eval ee))
     === subst id (lam eval (eval ee))  by  cong (subst id) (evalNAT eval ee)
     === subst eval (eval ee)           by  substLaw1 eval id (eval ee)
     === eval (flatE ee)                by  refl