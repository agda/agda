{-# OPTIONS --disable-positivity-check #-}

module univ where

import Logic.ChainReasoning
module Chain {A : Set}
             ( _==_ : A -> A -> Set)
             (refl : {x : A} -> x == x)
             (trans : {x y z : A} -> x == y -> y == z -> x == z) =
             Logic.ChainReasoning.Mono.Homogenous _==_ (\x -> refl) (\x y z -> trans)

data N1 : Set where
  T : N1

data N0 : Set where

data Sigma (A:Set)(B : A -> Set) : Set where
 Pair : (x:A) -> B x -> Sigma A B

rel : Set -> Set1 

rel A = A -> A -> Set

pred : Set -> Set1 

pred A = A -> Set

postulate
  N : Set
  _=N_ : rel N

Refl : (A:Set) -> rel A -> Set
Refl A R = {x : A} -> R x x 

Sym : (A:Set) -> rel A -> Set
Sym A R = {x y : A} -> R x y -> R y x

Trans : (A:Set) -> rel A -> Set
Trans A R = {x y z : A} -> R x y -> R y z -> R x z

Map : (A:Set) -> rel A -> (B:Set) -> rel B -> pred (A -> B)
Map A _R_ B _S_ f = {x y : A} -> x R y -> f x S f y



-- mutual inductive recursive definition of S and the functions _=S_, El, eq, and all the 
-- proofs on these functions

mutual

  infix 40 _==_ _=S_
  infixr 80 _<<_

  data S : Set where
    nat : S
    pi  : (A:S) -> (f:El A -> S) -> Map (El A) _==_ S _=S_ f -> S

  _=S'_ : rel S
  nat       =S' nat       = N1
  nat       =S' pi A f pf = N0
  pi _ _ _  =S' nat       = N0
  pi A F pF =S' pi B G pG =
      Sigma (A =S B) \ A=B -> (x : El B) -> F (A=B << x) =S G x

  data _=S_ (A B : S) : Set where
    eqS : A =S' B -> A =S B

  El' : S -> Set
  El' nat = N
  El' (pi A F pF) = 
   Sigma ((x : El A) -> El (F x))
         \f -> (x y : El A)(x=y : x == y) ->
               f x == pF x=y << f y

  data El (A : S) : Set where
    el : El' A -> El A

  _=='_ : {A : S} -> rel (El A)
  _=='_ {nat} (el x) (el y) = x =N y
  _=='_ {pi A F pF} (el (Pair f pf)) (el (Pair g pg)) =
        (x : El A) -> f x == g x

  data _==_ {A : S}(x y : El A) : Set where
    eq : x ==' y -> x == y

  _<<_ : {A B : S} -> A =S B -> El B -> El A
  _<<_ {nat} {nat} p x = x
  _<<_ {pi A F pF} {pi B G pG} (eqS (Pair A=B F=G)) (el (Pair g pg)) = el (Pair f pf)
    where
      B=A = symS A=B

      F=Gc : (x : El A) -> F x =S G (B=A << x)
      F=Gc x = 
        chain> F x
           === F (A=B << B=A << x)  by symS (pF (castlem A=B B=A x))
           === G (B=A << x)         by F=G _
        where open module C = Chain _=S_ refS transS

      f : (x : El A) -> El (F x)
      f x = F=Gc x << g (B=A << x)

      pf : (x y : El A)(p : x == y) -> f x == pF p << f y
      pf x y x=y = trans fx=ccgy ccgy=cfy
        where
          cx = B=A << x
          cy = B=A << y

          cx=cy : cx == cy
          cx=cy = p<< B=A x=y

          cgy : El (G cx)
          cgy = pG cx=cy << g cy

          gx=gy : g cx == cgy
          gx=gy = pg cx cy cx=cy

          ccgy : El (F x)
          ccgy = F=Gc x << cgy

          fx=ccgy : f x == ccgy
          fx=ccgy = p<< (F=Gc x) gx=gy

          cfy : El (F x)
          cfy = pF x=y << f y

          ccgy=cfy : ccgy == cfy
          ccgy=cfy = castlem2 (F=Gc x) (pF x=y)
                              (pG cx=cy) (F=Gc y)
                              (g cy)

  p<< : {A B : S}(A=B : A =S B) -> Map (El B) _==_ (El A) _==_ (_<<_ A=B)
  p<< {nat}{nat} _ x=y = x=y
  p<< {pi A F pF} {pi B G pG} (eqS (Pair A=B F=G))
        {el (Pair f pf)} {el (Pair g pg)} (eq f=g) = eq cf=cg
    where
      cf=cg : (x : El A) -> _
      cf=cg x = ?

  p<< {nat}      {pi _ _ _} (eqS ()) _
  p<< {pi _ _ _} {nat}      (eqS ()) _

  refS : Refl S _=S_
  refS {nat}       = eqS T
  refS {pi A F pF} = eqS (Pair refS \(x : El A) -> pF (castref refS x))

  transS : Trans S _=S_
  transS {nat}{nat}{nat} p q = p
  transS {nat}{nat}{pi _ _ _}      _      (eqS ())
  transS {nat}{pi _ _ _}{_}       (eqS ()) _
  transS {pi _ _ _}{nat}{_}       (eqS ()) _
  transS {pi _ _ _}{pi _ _ _}{nat} _      (eqS ())
  transS {pi A F pF}{pi B G pG}{pi C H pH}
         (eqS (Pair A=B F=G)) (eqS (Pair B=C G=H)) =
         eqS (Pair A=C F=H)
    where
      open module C = Chain _=S_ refS transS
      A=C = transS A=B B=C
      F=H : (x : El C) -> F (A=C << x) =S H x
      F=H x = -- transS lem3 (transS lem1 lem2)
        chain> F (A=C << x)
           === F (A=B << B=C << x) by symS (pF (casttrans A=B B=C A=C x))
           === G (B=C << x)        by F=G (B=C << x)
           === H x                 by G=H x

  symS : Sym S _=S_
  symS {nat}{nat} p                 = p
  symS {pi _ _ _}{nat} (eqS ())
  symS {nat}{pi _ _ _} (eqS ())
  symS {pi A F pF}{pi B G pg} (eqS (Pair A=B F=G)) = eqS (Pair B=A G=F)
    where
      open module C = Chain _=S_ refS transS
      B=A = symS A=B
      G=F : (x : El A) -> G (B=A << x) =S F x
      G=F x =
        chain> G (B=A << x)
           === F (A=B << B=A << x) by symS (F=G (B=A << x))
           === F x                 by pF (castlem A=B B=A x)

  pfi : {A B : S}(p q : A =S B)(x : El B) -> p << x == q << x
  pfi = ?

  castref : {A : S}(p : A =S A)(x : El A) -> p << x == x
  castref = ?

  casttrans : {A B C : S}(A=B : A =S B)(B=C : B =S C)(A=C : A =S C)(x : El C) ->
               A=B << B=C << x == A=C << x
  casttrans A=B B=C A=C x = ?

  castlem : {A B : S}(p : A =S B)(q : B =S A)(x : El A) ->
            p << q << x == x
  castlem {A}{B} p q x =
    chain> p << q << x
       === refS << x  by casttrans p q refS x
       === x          by castref refS x
    where open module C = Chain _==_ (ref {A}) (trans {A})

  castlem2 : {A B B' C : S}(A=B : A =S B)(A=B' : A =S B')(B=C : B =S C)(B'=C : B' =S C)
             (x : El C) ->
             A=B << B=C << x == A=B' << B'=C << x
  castlem2 A=B A=B' B=C B'=C x = ?

  ref : {A:S} -> Refl (El A) _==_
  ref {A}{x} = ?

  trans : {A:S} -> Trans (El A) _==_
  trans {A}{x}{y}{z} = ?

  sym : {A:S} -> Sym (El A) _==_
  sym {A}{x}{y} = ?




