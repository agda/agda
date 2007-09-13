module DeBruijnExSubstSized where

open import Prelude -- using (_∘_)       -- composition, identity
open import Data.Nat
open import Data.Maybe
open import Logic.Identity renaming (subst to subst≡)
import Logic.ChainReasoning
module Chain = Logic.ChainReasoning.Poly.Homogenous _≡_ (\x -> refl) (\x y z -> trans)
open Chain

open import DeBruijn

Size : Set
Size = Nat

-- untyped de Bruijn terms 
data LamE (A : Set) : Size -> Set where
    varE  : {ι : _} -> A -> LamE A (suc ι)
    appE  : {ι : _} -> LamE A ι -> LamE A ι -> LamE A (suc ι)
    absE  : {ι : _} -> LamE (Maybe A) ι -> LamE A (suc ι)
    flatE : {ι : _} -> LamE (LamE A ι) ι -> LamE A (suc ι)

-- functoriality of LamE 
lamE : {A B : Set} -> (A -> B) -> {ι : _} -> LamE A ι -> LamE B ι
lamE f {suc ι} (varE a)     = varE  (f a)
lamE f {suc ι} (appE t1 t2) = appE (lamE f t1) (lamE f t2)
lamE f {suc ι} (absE r)     = absE (lamE (fmap f) r)
lamE f {suc ι} (flatE r)    = flatE (lamE (lamE f) r)

eval : {ι : _} -> {A : Set} -> LamE A ι -> Lam A
eval {suc ι} (varE a)     = var a
eval {suc ι} (appE t1 t2) = app (eval t1) (eval t2)
eval {suc ι} (absE r)     = abs (eval r)
eval {suc ι} (flatE r)    = subst (eval) (eval r)

evalNAT : {A B : Set}(f : A -> B) -> {ι : _} -> (t : LamE A ι) -> 
  eval (lamE f t) ≡ lam f (eval t)
evalNAT f {suc ι} (varE a)     = refl
evalNAT f {suc ι} (appE t1 t2) =
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
evalNAT f {suc ι} (absE r) =
  chain> eval (lamE f (absE r))
     === eval (absE (lamE (fmap f) r))   by  refl
     === abs (eval (lamE (fmap f) r))    by  refl
     === abs (lam (fmap f) (eval r))     by  cong abs (evalNAT (fmap f) r)
     === lam f (abs (eval r))            by  refl
     === lam f (eval (absE r))           by  refl
evalNAT f {suc ι} (flatE r) = 
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

evalNATcor : {A : Set}{ι : _}(ee : LamE (LamE A ι) ι) ->
  subst id (eval (lamE eval ee)) ≡ eval (flatE ee)
evalNATcor ee = 
  chain> subst id (eval (lamE eval ee))
     === subst id (lam eval (eval ee))  by  cong (subst id) (evalNAT eval ee)
     === subst eval (eval ee)           by  substLaw1 eval id (eval ee)
     === eval (flatE ee)                by  refl