{-# OPTIONS --universe-polymorphism --guardedness #-}
-- {-# OPTIONS --verbose tc.constr.findInScope:15 #-}
-- {-# OPTIONS --verbose tc.meta.eta:20 #-}
-- {-# OPTIONS --verbose tc.conv.term:20 #-}
-- {-# OPTIONS --verbose tc.meta.assign:70 #-}
-- {-# OPTIONS --verbose tc.eta.rec:70 #-}
-- {-# OPTIONS --verbose tc.sig.inst:30 #-}

module InstanceArguments.11-monads where

open import Effect.Monad using (RawMonad; module RawMonad)
open import Effect.Monad.Indexed using (RawIMonad; module RawIMonad)
--open import Effect.Applicative.Indexed using ()
-- identityMonad often makes monadic code ambiguous.
--open import Effect.Monad.Identity using (IdentityMonad)
open import Effect.Monad.Partiality using (_⊥; now; isNow; never; run_for_steps) renaming (monad to partialityMonad)
open import Effect.Monad.State using (RawMonadState)
open import Effect.Applicative.Indexed using (IFun)
open import Function using (_$_)
open import Function.Reasoning
open import Level using (zero; Level)
--open import Data.Unit hiding (_≟_)
open import Data.Bool using (if_then_else_)
open import Data.Nat using (ℕ; _≟_; _+_; suc; _*_)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Data.List using (List; _∷_; []; [_]; null)
open import Data.List.Effectful using () renaming (monad to listMonad)
--open import Data.Product

module RawMonadExt {li f} {I : Set li} {M : IFun I f} (m : RawIMonad M) where
  -- _>>=_ : ∀ {i j k A B} → M i j A → (A → M j k B) → M i k B
  -- _>>=_ {i} {j} {k} {A} {B} = RawIMonad._>>=_ {li} {f} {I} {M} m {i} {j} {k} {A} {B}

instance i⊥ = partialityMonad
         iList = listMonad

stateMonad : (Set → Set) → Set₁
stateMonad = RawMonadState ℕ

nToList : ℕ → List ℕ
nToList 0 = [ 0 ]
nToList (suc n) = n ∷ nToList n

test′ : ℕ → (List ℕ) ⊥
test′ k = let open RawMonad partialityMonad
          in do x ← pure (k ∷ k + 1 ∷ [])
                pure x

test2′ : ℕ → (List ℕ) ⊥
test2′ k =  let open RawMonad partialityMonad
                open RawMonad listMonad using () renaming (_>>=_ to _l>>=_)
            in do x ← pure [ k ]
                  if ⌊ k ≟ 4 ⌋ then pure (x l>>= nToList) else never

open RawMonad {{...}}
open RawMonadExt {{...}}

test1 : ℕ → ℕ ⊥
test1 k =  do x ← pure k
              if ⌊ x ≟ 4 ⌋ then pure 10 else never

test2 : ℕ → (List ℕ) ⊥
test2 k =  do x ← pure [ k ]
              if ⌊ k ≟ 4 ⌋ then pure ((x ∶ List ℕ) >>= nToList) else never
test' : ℕ → (List ℕ) ⊥
test' k = do x ← pure (k ∷ k + 1 ∷ [])
             if null x then never else pure (x >>= nToList)

test3 : List ℕ
test3 = do x ← 1 ∷ 2 ∷ 3 ∷ []
           pure $ x + 1
