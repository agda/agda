{-# OPTIONS --guarded #-}
module TickJoin where

open import Agda.Builtin.Nat

primitive primLockUniv : Set₁
postulate Tick : primLockUniv

▹_ : ∀ {l} → Set l → Set l
▹_ A = (@tick x : Tick) → A

join : ∀ {A : Set} → ▹ ▹ A → ▹ A
join x tic = x tic tic
