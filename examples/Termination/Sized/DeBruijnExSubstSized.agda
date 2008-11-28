{-# OPTIONS --sized-types #-} -- --no-coverage-check #-}

module DeBruijnExSubstSized where

open import Data.Function -- using (_∘_)       -- composition, identity
open import Data.Nat
open import Data.Maybe
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import Size

open import DeBruijn

-- untyped de Bruijn terms 
data LamE (A : Set) : Size -> Set where
    varE  : {ι : _} -> A -> LamE A (↑ ι)
    appE  : {ι : _} -> LamE A ι -> LamE A ι -> LamE A (↑ ι)
    absE  : {ι : _} -> LamE (Maybe A) ι -> LamE A (↑ ι)
    flatE : {ι : _} -> LamE (LamE A ι) ι -> LamE A (↑ ι)

-- functoriality of LamE 
lamE : {A B : Set} -> (A -> B) -> {ι : _} -> LamE A ι -> LamE B ι
lamE f (varE a)     = varE  (f a)
lamE f (appE t1 t2) = appE (lamE f t1) (lamE f t2)
lamE f (absE r)     = absE (lamE (fmap f) r)
lamE f (flatE r)    = flatE (lamE (lamE f) r)

eval : {ι : _} -> {A : Set} -> LamE A ι -> Lam A
eval (varE a)     = var a
eval (appE t1 t2) = app (eval t1) (eval t2)
eval (absE r)     = abs (eval r)
eval (flatE r)    = subst (eval) (eval r)


-- Theorem (naturality of eval):  eval ∘ lamE f ≡ lam f ∘ eval
evalNAT : {A B : Set}(f : A -> B) -> {ι : _} -> (t : LamE A ι) -> 
  eval (lamE f t) ≡ lam f (eval t)
evalNAT f (varE a)     = ≡-refl
evalNAT f (appE t1 t2) = begin
  eval (lamE f (appE t1 t2))
     ≡⟨ ≡-refl ⟩
  eval (appE (lamE f t1) (lamE f t2))
     ≡⟨ ≡-refl ⟩
  app (eval (lamE f t1)) (eval (lamE f t2))
     ≡⟨ ≡-cong (\ x -> app x (eval (lamE f t2))) (evalNAT f t1) ⟩
  app (lam f (eval t1))  (eval (lamE f t2))
     ≡⟨ ≡-cong (\ x -> app (lam f (eval t1)) x)  (evalNAT f t2) ⟩
  app (lam f (eval t1))  (lam f (eval t2))
     ≡⟨ ≡-refl ⟩
  lam f (app (eval t1) (eval t2))
     ≡⟨ ≡-refl ⟩
  lam f (eval (appE t1 t2))
     ∎
evalNAT f (absE r) = begin
  eval (lamE f (absE r))
     ≡⟨ ≡-refl ⟩
  eval (absE (lamE (fmap f) r))
     ≡⟨ ≡-refl ⟩
  abs (eval (lamE (fmap f) r)) 
     ≡⟨ ≡-cong abs (evalNAT (fmap f) r) ⟩
  abs (lam (fmap f) (eval r))
     ≡⟨ ≡-refl ⟩
  lam f (abs (eval r))
     ≡⟨ ≡-refl ⟩
  lam f (eval (absE r))
     ∎
-- in the following case, one manual size annotation is needed on the RHS
-- it is for the first application of the I.H.
evalNAT f (flatE {ι} r) = begin
  eval (lamE f (flatE r))
     ≡⟨ ≡-refl ⟩
  eval (flatE (lamE (lamE f) r))
     ≡⟨ ≡-refl ⟩
  subst eval (eval (lamE (lamE f) r))
     ≡⟨ ≡-cong (subst (eval {ι})) (evalNAT (lamE f) r) ⟩
  subst eval (lam (lamE f) (eval r))
     ≡⟨ substLaw1 (lamE f) eval (eval r) ⟩
  subst (eval ∘ lamE f) (eval r)
     ≡⟨ substExt (evalNAT f) (eval r) ⟩
  subst (lam f ∘ eval) (eval r)
     ≡⟨ substLaw2 f eval (eval r) ⟩
  lam f (subst eval (eval r))
     ≡⟨ ≡-refl ⟩
  lam f (eval (flatE r))
     ∎

evalNATcor : {A : Set}{ι : _}(ee : LamE (LamE A ι) ι) ->
  subst id (eval (lamE eval ee)) ≡ eval (flatE ee)
evalNATcor ee = begin
  subst id (eval (lamE eval ee))
     ≡⟨ ≡-cong (subst id) (evalNAT eval ee) ⟩
  subst id (lam eval (eval ee))
     ≡⟨ substLaw1 eval id (eval ee) ⟩
  subst eval (eval ee)
     ≡⟨ ≡-refl ⟩
  eval (flatE ee)
     ∎
