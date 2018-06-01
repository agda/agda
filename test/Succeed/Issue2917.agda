{-# OPTIONS --allow-unsolved-metas #-}
open import Agda.Builtin.Size

mutual

  data Nat (i : Size) : Set where
    zero : Nat i
    suc  : Nat′ i → Nat i

  data Nat′ (i : Size) : Set where
    [_] : {j : Size< i} → Nat j → Nat′ i

size : ∀ {i} → Nat′ i → Size
size ([_] {j} _) = {!j!}

unbox : ∀ {i} (n : Nat′ i) → Nat (size n)
unbox [ n ] = n

postulate
  _ _ _ _ _ _ : Set
