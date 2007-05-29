module List where

data Bool : Set where
  true : Bool
  false : Bool

if_then_else_ : {A : Set} -> Bool -> A -> A -> A
if true  then x else y = x
if false then x else y = y

boolElim : (P : Bool -> Set) -> P true -> P false -> (b : Bool) -> P b
boolElim P t f true  = t
boolElim P t f false = f

data False : Set where
data True : Set where
  tt : True

data Or (A B : Set) : Set where
  inl : (a : A) -> Or A B
  inr : (b : B) -> Or A B

orElim : {A B : Set}
    -> (C : Or A B -> Set)
    -> (cl : (a : A) -> C(inl a))
    -> (cr : (b : B) -> C(inr b))
    -> (ab : Or A B)
    -> C ab
orElim {A} {B} C cl cr (inl a) = cl a
orElim {A} {B} C cl cr (inr b) = cr b

data Rel(A : Set) : Set1 where
  rel : (A -> A -> Set) -> Rel A

_is_than_ : {A : Set} -> A -> Rel A -> A -> Set
x is rel f than y = f x y

data Acc {A : Set} (less : Rel A) (x : A) : Set where
  acc : ((y : A) -> y is less than x -> Acc less y) -> Acc less x

data WO {A : Set} (less : Rel A) : Set where
  wo : ((x : A) -> Acc less x) -> WO less

data Nat : Set where
  Z : Nat
  S : Nat -> Nat

eqNat : Nat -> Nat -> Set
eqNat Z Z = True
eqNat (S m) (S n) = eqNat m n
eqNat _ _ = False

substEqNat : (P : Nat -> Set) -> (a b : Nat) -> (e : eqNat a b) -> (P a) -> P b
substEqNat P Z Z e pa = pa
substEqNat P (S x) (S x') e pa = substEqNat (\n -> P(S n)) x  x'  e  pa

ltNat : Nat -> Nat -> Set
ltNat    Z     Z  = False
ltNat    Z  (S n) = True
ltNat (S m) (S n) = ltNat m n
ltNat (S m)    Z  = False

ltZ-elim : (n : Nat) -> ltNat n Z -> {whatever : Set} -> whatever
ltZ-elim Z     ()
ltZ-elim (S _) ()

transNat : (x  y  z : Nat) -> ltNat x y -> ltNat y z -> ltNat x z
transNat x     y     Z     x<y y<z  = ltZ-elim y y<z
transNat x     Z     (S z) x<Z Z<Sz = ltZ-elim x x<Z
transNat Z     (S y) (S z) tt  y<z  = tt
transNat (S x) (S y) (S z) x<y y<z  = transNat x y z x<y y<z

ltNat-S-Lemma : (x : Nat) -> ltNat x (S x)
ltNat-S-Lemma Z     = tt
ltNat-S-Lemma (S x) = ltNat-S-Lemma x

ltNat-S-Lemma2 : (y z : Nat) -> ltNat y (S z) -> Or (eqNat z y) (ltNat y z)
ltNat-S-Lemma2 Z Z h = inl tt
ltNat-S-Lemma2 Z (S x) h = inr tt
ltNat-S-Lemma2 (S x) (S x') h = ltNat-S-Lemma2 x  x' h

ltNatRel : Rel Nat
ltNatRel = rel ltNat

less = ltNatRel

acc-Lemma1 : (x y : Nat) -> Acc less x -> eqNat x y -> Acc less y
acc-Lemma1 x y a e = substEqNat (Acc less ) x  y  e  a

acc-Lemma2 : (x y : Nat) -> Acc less x -> ltNat y x -> Acc less y
acc-Lemma2 x y (acc h) l = h y  l

-- postulate woltNat' : (n : Nat) -> Acc less n
woltNat' : (n : Nat) -> Acc less n
woltNat' Z     = acc (\y y<Z -> ltZ-elim y y<Z)
woltNat' (S x) = acc (\y y<Sx -> orElim (\w -> Acc less y) (\e -> substEqNat (Acc less ) x  y  e  (woltNat' x ) ) (acc-Lemma2 x y (woltNat' x)) (ltNat-S-Lemma2 y x y<Sx ))

woltNat : WO ltNatRel
woltNat = wo woltNat'

postulate le : Nat -> Nat -> Bool
postulate gt : Nat -> Nat -> Bool

data List (A : Set) : Set where
  nil  : List A
  cons : (x : A) -> (xs : List A) -> List A

_++_ : {A : Set} -> List A -> List A -> List A
nil         ++ ys = ys
(cons x xs) ++ ys = cons x (xs ++ ys)

length : {A : Set} -> List A -> Nat
length nil         = Z
length (cons x xs) = S (length xs)

filter : {A : Set} -> (A -> Bool) -> List A -> List A
filter p nil = nil
filter p (cons x xs) = if p x then cons x rest else rest
  where rest = filter p xs

filterLemma
  :  {A : Set} -> (p : A -> Bool) -> (xs : List A)
  -> length (filter p xs) is less than S (length xs)
filterLemma p nil         = tt
filterLemma p (cons x xs) =
  boolElim (\px -> length (if px then cons x (filter p xs)
                                 else (filter p xs))
                   is less than S (S (length xs)))
           (filterLemma p xs)
           (transNat (length (filter p xs)) (S (length xs)) (S (S (length xs)))
                     (filterLemma p xs) (ltNat-S-Lemma (length xs )))
           (p x)

qs : List Nat -> List Nat
qs nil         = nil
qs (cons x xs) = qs (filter (le x) xs)
                 ++ cons x nil
                 ++ qs (filter (gt x) xs)

data Measure : Set1 where
  μ : {M : Set} -> {rel : Rel M} -> (ord : WO rel) -> Measure

down1-measure : Measure
down1-measure = μ woltNat

qs-2-1-hint = \(x : Nat) -> \(xs : List Nat) -> filterLemma (le x) xs
qs-2-2-hint = \(x : Nat) -> \(xs : List Nat) -> filterLemma (gt x) xs
