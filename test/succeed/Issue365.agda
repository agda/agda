-- {-# OPTIONS -v tc.cover.cover:10 -v tc.cover.splittree:100 -v tc.cover.strategy:100 -v tc.cc:100 #-}
module Issue365 where

{- Basic data types -}

data Nat : Set where
 zero : Nat
 succ : Nat -> Nat

data Fin : Nat -> Set where
 fzero : {n : Nat} -> Fin (succ n)
 fsucc : {n : Nat} -> Fin n -> Fin (succ n)

data Vec (A : Set) : Nat -> Set where
 []   : Vec A zero
 _::_ : {n : Nat} -> A -> Vec A n -> Vec A (succ n)

data _==_ {A : Set} (x : A) : A -> Set where
 refl : x == x

{- Function composition -}

_◦_ : {A : Set} {B : A -> Set} {C : (x : A) -> B x -> Set}
     (f : {x : A} (y : B x) -> C x y) (g : (x : A) -> B x)
     (x : A) -> C x (g x)
(f ◦ g) x = f (g x)

{- Indexing and tabulating -}

_!_ : {n : Nat} {A : Set} -> Vec A n -> Fin n -> A
[]        ! ()
(x :: xs) ! fzero     = x
(x :: xs) ! (fsucc i) = xs ! i

tabulate : {n : Nat} {A : Set} -> (Fin n -> A) -> Vec A n
tabulate {zero}   f = []
tabulate {succ n} f = f fzero :: tabulate (f ◦ fsucc)

lem-tab-! : forall {A n} (xs : Vec A n) -> tabulate (_!_ xs) == xs
lem-tab-! {A} {zero}   [] = refl
lem-tab-! {A} {succ n} (x :: xs) with tabulate (_!_ xs) | lem-tab-! xs
lem-tab-! {A} {succ _} (x :: xs) | .xs | refl = refl
