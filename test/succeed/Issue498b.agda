
module Issue498b where

record ⊤ : Set where
  constructor tt

postulate
  U   : Set → Set
  pr  : ∀ {A} → A → U A
  _*_ : ∀ {A B} → U A → (A → U B) → U B

module M (I : Set)(J : I → Set)(K : (i : I)(j : J i) → Set) where

  data D (P : I → Set) : I → Set where
    r : ∀ {i} → P i → D P i
    d : (i : I)(j : J i)
        (f : K i j → D P i) → D P i

  module N (e : (i : I)(j : J i) → U (K i j)) where

    du : ∀ {P}{i : I} → D P i → U (P i)
    du (r p)     = pr p
    du (d i j f) = e i j * λ k → du (f k)


data j : ⊤ → Set where
  cj : j _

k : (i : ⊤)(j : j i) → Set
k _ j = ⊤

e : (i : ⊤)(j : j i) → U (k i j)
e tt cj = pr tt

open M ⊤ j k
open N e
