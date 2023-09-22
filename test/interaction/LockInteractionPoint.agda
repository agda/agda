{-# OPTIONS --guarded #-}
module LockInteractionPoint where

primitive primLockUniv : Set₁
postulate Tick : primLockUniv

ex : ∀ {A : Set} → (@tick Tick → A) → @tick Tick → A
ex f x = f {! !}
