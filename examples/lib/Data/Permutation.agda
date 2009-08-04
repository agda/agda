
module Data.Permutation where

{-

open import Prelude
open import Data.Fin as Fin hiding (_==_; _<_)
open import Data.Nat
open import Data.Vec
open import Logic.Identity
open import Logic.Base
import Logic.ChainReasoning

-- What is a permutation?
-- Answer 1: A bijection between Fin n and itself

data Permutation (n : Nat) : Set where
  permutation :
    (π π⁻¹ : Fin n -> Fin n) ->
    (forall {i} -> π (π⁻¹ i) ≡ i) ->
    Permutation n

module Permutation {n : Nat}(P : Permutation n) where

  private
    π' : Permutation n -> Fin n -> Fin n
    π' (permutation x _ _) = x

    π⁻¹' : Permutation n -> Fin n -> Fin n
    π⁻¹' (permutation _ x _) = x

    proof : (P : Permutation n) -> forall {i} -> π' P (π⁻¹' P i) ≡ i
    proof (permutation _ _ x) = x

  π : Fin n -> Fin n
  π      = π' P

  π⁻¹ : Fin n -> Fin n
  π⁻¹         = π⁻¹' P

  module Proofs where

    ππ⁻¹-id : {i : Fin n} -> π (π⁻¹ i) ≡ i
    ππ⁻¹-id = proof P

    open module Chain = Logic.ChainReasoning.Poly.Homogenous _≡_ (\x -> refl) (\x y z -> trans)

    π⁻¹-inj : (i j : Fin n) -> π⁻¹ i ≡ π⁻¹ j -> i ≡ j
    π⁻¹-inj i j h =
      chain> i
         === π (π⁻¹ i)     by sym ππ⁻¹-id
         === π (π⁻¹ j)     by cong π h
         === j          by ππ⁻¹-id

    -- Generalise
    lem : {n : Nat}(f g : Fin n -> Fin n)
          -> (forall i -> f (g i) ≡ i)
          -> (forall i -> g (f i) ≡ i)
    lem {zero}  f g inv ()
    lem {suc n} f g inv i  = ?
      where
        gz≠gs : {i : Fin n} -> g fzero ≢ g (fsuc i)
        gz≠gs {i} gz=gs = fzero≠fsuc $
          chain> fzero
             === f (g fzero)     by sym (inv fzero)
             === f (g (fsuc i))  by cong f gz=gs
             === fsuc i          by inv (fsuc i)

        z≠f-thin-gz : {i : Fin n} -> fzero ≢ f (thin (g fzero) i)
        z≠f-thin-gz {i} z=f-thin-gz = ?
--        f (g fzero)
--        = fzero
--        = f (thin (g fzero) i)

        g' : Fin n -> Fin n
        g' j = thick (g fzero) (g (fsuc j)) gz≠gs

        f' : Fin n -> Fin n
        f' j = thick fzero (f (thin (g fzero) j)) ?

        g'f' : forall j -> g' (f' j) ≡ j
        g'f' = lem {n} f' g' ?

    π⁻¹π-id : forall {i} -> π⁻¹ (π i) ≡ i
    π⁻¹π-id = ?

-- Answer 2: A Vec (Fin n) n with no duplicates

{-
infixr 40 _◅_ _↦_,_
infixr 20 _○_

data Permutation : Nat -> Set where
  ε   : Permutation zero
  _◅_ : {n : Nat} -> Fin (suc n) -> Permutation n -> Permutation (suc n)

_↦_,_ : {n : Nat}(i j : Fin (suc n)) -> Permutation n -> Permutation (suc n)
fzero  ↦ j , π           = j ◅ π
fsuc i ↦ j , j' ◅ π = thin j j' ◅ i ↦ ? , π

indices : {n : Nat} -> Permutation n -> Vec (Fin n) n
indices  ε     = []
indices (i ◅ π) = i :: map (thin i) (indices π)

-- permute (i ◅ π) xs with xs [!] i where
--   permute₁ (i ◅ π) .(insert i x xs) (ixV x xs) = x :: permute π xs

permute : {n : Nat}{A : Set} -> Permutation n -> Vec A n -> Vec A n
permute (i ◅ π) xs = permute' π i xs (xs [!] i)
  where
    permute' : {n : Nat}{A : Set} -> Permutation n -> (i : Fin (suc n))(xs : Vec A (suc n)) ->
               IndexView i xs -> Vec A (suc n)
    permute' π i .(insert i x xs') (ixV x xs') = x :: permute π xs'

delete : {n : Nat} -> Fin (suc n) -> Permutation (suc n) -> Permutation n
delete          fzero    (j ◅ π) = π
delete {zero}  (fsuc ())  _
delete {suc _} (fsuc i)  (j ◅ π) = ? ◅ delete i π

identity : {n : Nat} -> Permutation n
identity {zero } = ε
identity {suc n} = fzero ◅ identity

_⁻¹ : {n : Nat} -> Permutation n -> Permutation n
ε      ⁻¹ = ε
(i ◅ π) ⁻¹ = ?

_○_ : {n : Nat} -> Permutation n -> Permutation n -> Permutation n
ε      ○ π₂ = ε
i ◅ π₁ ○ π₂ = (indices π₂ ! i) ◅ (π₁ ○ delete i π₂)
-}

-}
