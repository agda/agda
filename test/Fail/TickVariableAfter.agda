{-# OPTIONS --guarded #-}
module TickVariableAfter where

open import Agda.Builtin.Nat

primitive primLockUniv : Set₁
postulate Tick : primLockUniv

▹_ : ∀ {l} → Set l → Set l
▹_ A = (@tick x : Tick) → A

illegal : ∀ {A : Set} → @lock Tick → ▹ A → A
illegal tic later = later tic
