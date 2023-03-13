{-# OPTIONS --guarded #-}
module TickVariablesAfter where

open import Agda.Builtin.Nat

primitive primLockUniv : Set₁
postulate Tick : primLockUniv

▹_ : ∀ {l} → Set l → Set l
▹_ A = (@tick x : Tick) → A

illegal : ∀ {A B : Set} → @lock Tick → (A → ▹ B) → A → B
illegal tic func arg = func arg tic
