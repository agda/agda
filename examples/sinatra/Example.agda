
module Example where

open import Prelude
import Typed

data Data : Set where
  nat  : Data
  bool : Data

Datatype : Data -> List (List Data)
Datatype nat  = ε ◄ ε ◄ (ε ◄ nat)
Datatype bool = ε ◄ ε ◄ ε

data Effect : Set where

data _⊆_ : Effect -> Effect -> Set where
  refl⊆  : forall {M} -> M ⊆ M

Monad : Effect -> Set -> Set
Monad e A = A

return : forall {M A} -> A -> Monad M A
return x = x

map    : forall {M A B} -> (A -> B) -> Monad M A -> Monad M B
map f m = f m

join   : forall {M A} -> Monad M (Monad M A) -> Monad M A
join m = m

morph  : forall {M N} -> M ⊆ N -> (A : Set) -> Monad M A -> Monad N A
morph _ A x = x

open module TT =
       Typed Data Datatype
             Effect _⊆_
             Monad
             (\{M A} -> return {M}{A})
             (\{M A B} -> map {M}{A}{B})
             (\{M A} -> join {M}{A})
             morph

zero : forall {M Γ} -> InV M Γ (TyCon nat)
zero = con (tl hd) ⟨⟩

suc : forall {M Γ} -> InV M Γ (TyCon nat) -> InV M Γ (TyCon nat)
suc n = con hd (⟨⟩ ◃ n)

true : forall {M Γ} -> InV M Γ (TyCon bool)
true = con hd ⟨⟩

false : forall {M Γ} -> InV M Γ (TyCon bool)
false = con (tl hd) ⟨⟩
