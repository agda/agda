{-# OPTIONS --universe-polymorphism #-}
-- {-# OPTIONS --verbose tc.constr.findInScope:15 #-}
-- {-# OPTIONS --verbose tc.meta.eta:20 #-}
-- {-# OPTIONS --verbose tc.conv.term:20 #-}
-- {-# OPTIONS --verbose tc.meta.assign:70 #-}
-- {-# OPTIONS --verbose tc.eta.rec:70 #-}
-- {-# OPTIONS --verbose tc.sig.inst:30 #-}

module 11-monads where

open import Category.Monad using (RawMonad; module RawMonad)
open import Category.Monad.Indexed using (RawIMonad; module RawIMonad)
--open import Category.Applicative.Indexed using ()
-- identityMonad often makes monadic code ambiguous.
--open import Category.Monad.Identity using (IdentityMonad)
open import Category.Monad.Partiality using (_⊥; now; isNow; never; run_for_steps) renaming (monad to partialityMonad)
open import Category.Monad.State using (StateMonad)
open import Category.Applicative.Indexed using (IFun)
open import Function using (_$_)
open import Level using (zero; Level)
--open import Data.Unit hiding (_≟_)
open import Data.Bool using (if_then_else_)
open import Data.Nat using (ℕ; _≟_; _+_; suc; _*_)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Data.List using (List; _∷_; []; [_]; null) renaming (monad to listMonad)
--open import Data.Product

module RawMonadExt {li f} {I : Set li} {M : IFun I f} (m : RawIMonad M) where 
  bind : ∀ {i j k A B} → M i j A → (A → M j k B) → M i k B
  bind {i} {j} {k} {A} {B} = RawIMonad._>>=_ {li} {f} {I} {M} m {i} {j} {k} {A} {B}

  syntax bind m (λ x → c) = do x ← m then c

stateMonad = StateMonad ℕ

nToList : ℕ → List ℕ
nToList 0 = [ 0 ]
nToList (suc n) = n ∷ nToList n

test′ : ℕ → (List ℕ) ⊥
test′ k = let open RawMonad partialityMonad
              open RawMonadExt partialityMonad 
          in do x ← return (k ∷ k + 1 ∷ []) then
             return x

test2′ : ℕ → (List ℕ) ⊥
test2′ k =  let open RawMonad partialityMonad
                open RawMonadExt partialityMonad 
                open RawMonad listMonad using () renaming (_>>=_ to _l>>=_) 
            in do x ← return [ k ] then
                  if ⌊ k ≟ 4 ⌋ then return (x l>>= nToList) else never

open RawMonad {{...}}
open RawMonadExt {{...}}

test1 : ℕ → ℕ ⊥
test1 k =  do x ← return k then
           if ⌊ x ≟ 4 ⌋ then return 10 else never

test2 : ℕ → (List ℕ) ⊥
test2 k =  do x ← return [ k ] then
           if ⌊ k ≟ 4 ⌋ then return (x >>= nToList) else never 
test' : ℕ → (List ℕ) ⊥
test' k = do x ← return (k ∷ k + 1 ∷ []) then
          if null x then never else return (x >>= nToList)
          
test3 : List ℕ
test3 = do x ← 1 ∷ 2 ∷ 3 ∷ [] then
        return $ x + 1
