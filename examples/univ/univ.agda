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

Refl : {A:Set} -> rel A -> Set
Refl {A} R = {x : A} -> R x x 

Sym : {A:Set} -> rel A -> Set
Sym {A} R = {x y : A} -> R x y -> R y x

Trans : {A:Set} -> rel A -> Set
Trans {A} R = {x y z : A} -> R x y -> R y z -> R x z

Map : (A:Set) -> rel A -> (B:Set) -> rel B -> pred (A -> B)
Map A _R_ B _S_ f = {x y : A} -> x R y -> f x S f y

postulate
  N : Set
  _=N_ : rel N
  refN : Refl _=N_
  symN : Sym _=N_
  transN : Trans _=N_


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
         \f -> {x y : El A}(x=y : x == y) ->
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
  _<<_ {pi A F pF} {pi B G pG} (eqS (Pair A=B F=G)) (el (Pair g pg)) =
    el (Pair f (\{x}{y} -> pf x y))
    where
      B=A = symS A=B

      F=Gc : (x : El A) -> F x =S G (B=A << x)
      F=Gc x = 
        transS (transS refS (symS (pF (castlem A=B (symS A=B) x))))
        (F=G (symS A=B << x))

--         chain> F x
--            === F (A=B << B=A << x)  by symS (pF (castlem A=B B=A x))
--            === G (B=A << x)         by F=G (B=A << x)
--         where
--           open module C = Chain _=S_ refS transS

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
          gx=gy = pg cx=cy

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
      open module C = Logic.ChainReasoning.Mono.Homogenous _=S_ (\x -> refS) (\x y z -> transS)
      B=A = symS A=B

      F=Gc : (x : El A) -> F x =S G (B=A << x)
      F=Gc x = 
        chain> F x
           === F (A=B << B=A << x)  by symS (pF (castlem A=B B=A x))
           === G (B=A << x)         by F=G _

      cf=cg : (x : El A) -> F=Gc x << f (B=A << x)
                         == F=Gc x << g (B=A << x)
      cf=cg x = p<< (F=Gc x) (f=g (B=A << x))

  p<< {nat}      {pi _ _ _} (eqS ()) _
  p<< {pi _ _ _} {nat}      (eqS ()) _

  refS : Refl _=S_
  refS {nat}       = eqS T
  refS {pi A F pF} = eqS (Pair refS \(x : El A) -> pF (castref refS x))

  transS : Trans _=S_
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
      F=H x =
        chain> F (A=C << x)
           === F (A=B << B=C << x) by symS (pF (casttrans A=B B=C A=C x))
           === G (B=C << x)        by F=G (B=C << x)
           === H x                 by G=H x

  symS : Sym _=S_
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
  pfi {nat}{nat} _ _ x = ref
  pfi {nat}{pi _ _ _} (eqS ()) _ _
  pfi {pi _ _ _}{nat} (eqS ()) _ _
  pfi {pi A F pF}{pi B G pG} (eqS (Pair A=B1 F=G1)) (eqS (Pair A=B2 F=G2))
      (el (Pair f pf)) = eq f1=f2
    where
      B=A1 = symS A=B1
      B=A2 = symS A=B2

      f1=f2 : (x : El A) -> _ << f (B=A1 << x) == _ << f (B=A2 << x)
      f1=f2 x =
        chain> _ << f (B=A1 << x)
           === _ << _ << f (B=A2 << x) by p<< _ lem2
           === _ << f (B=A2 << x)      by casttrans _ _ _ _
        where
          open module C = Chain _==_ (ref {F x}) (trans {F x})
          lem1 : B=A1 << x == B=A2 << x
          lem1 = pfi B=A1 B=A2 x

          lem2 : f (B=A1 << x) == _ << f (B=A2 << x)
          lem2 = pf lem1

  castref : {A : S}(p : A =S A)(x : El A) -> p << x == x
  castref {nat} p x = ref
  castref {pi A F pF} (eqS (Pair A=A F=F)) (el (Pair f pf)) = eq cf=f
    where
      A=A' = symS A=A
      cf=f : (x : El A) -> _ << f (A=A' << x) == f x
      cf=f x =
        chain> Fx=Fcx << f (A=A' << x)
           === Fx=Fcx << _ << f x by p<< Fx=Fcx lem2
           === refS << f x        by casttrans _ _ _ (f x)
           === f x                by castref _ (f x)
        where
          Fx=Fcx = _
          open module C = Chain _==_ (ref {F x}) (trans {F x})
          lem1 : A=A' << x == x
          lem1 = castref A=A' x

          lem2 : f (A=A' << x) == _ << f x
          lem2 = pf lem1

  casttrans : {A B C : S}(A=B : A =S B)(B=C : B =S C)(A=C : A =S C)(x : El C) ->
               A=B << B=C << x == A=C << x
  casttrans {nat}{nat}{nat} _ _ _ x = ref
  casttrans {nat}{nat}{pi _ _ _}      _      (eqS ()) _ _
  casttrans {nat}{pi _ _ _}{_}       (eqS ()) _ _ _
  casttrans {pi _ _ _}{nat}{_}       (eqS ()) _ _ _
  casttrans {pi _ _ _}{pi _ _ _}{nat} _      (eqS ()) _ _
  casttrans {pi A F pF}{pi B G pG}{pi C H pH}
            (eqS (Pair A=B F=G))(eqS (Pair B=C G=H))(eqS (Pair A=C F=H))
            (el (Pair h ph)) = eq prf
    where
      B=A = symS A=B
      C=B = symS B=C
      C=A = symS A=C

      prf : (x : El A) -> _ << _ << h (C=B << B=A << x) == _ << h (C=A << x)
      prf x =
        chain> Fx=Gcx << Gcx=Hccx << h (C=B << B=A << x)
           === Fx=Hccx << h (C=B << B=A << x) by casttrans _ _ _ _
           === Fx=Hccx << _ << h (C=A << x) by p<< _ (ph (casttrans C=B B=A C=A x))
           === Fx=Hcx << h (C=A << x)  by casttrans _ _ _ _
        where
          Fx=Gcx   = _
          Gcx=Hccx = _
          Fx=Hccx  = transS (lemF=Gc A=B pF pG F=G _)
                            (lemF=Gc B=C pG pH G=H _)
          Fx=Hcx   = _
          open module C = Chain _==_ (ref {F x}) (trans {F x})

  lemF=Gc : {A B : S}(A=B : A =S B)
            {F : El A -> S}(pF : Map (El A) _==_ S _=S_ F)
            {G : El B -> S}(pG : Map (El B) _==_ S _=S_ G)
            (F=G : (x : El B) -> F (A=B << x) =S G x)
            (x : El A) -> F x =S G (symS A=B << x)
  lemF=Gc A=B {F} pF {G} pG F=G x = 
    chain> F x
       === F (A=B << B=A << x)  by symS (pF (castlem A=B B=A x))
       === G (B=A << x)         by F=G _
    where
      open module C = Chain _=S_ refS transS
      B=A = symS A=B

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
  castlem2 {A} p p' q q' x =
    chain> p << q       << x
       === transS p  q  << x  by casttrans _ _ _ x
       === transS p' q' << x  by pfi _ _ _
       === p' << q'     << x  by sym (casttrans _ _ _ x)
    where open module C = Chain _==_ (ref {A}) (trans {A})

  ref : {A:S} -> Refl {El A} _==_
  ref {nat}      {el n}           = eq refN
  ref {pi A F pF}{el (Pair f pf)} = eq f=f
    where
      f=f : (x : El A) -> f x == f x
      f=f x = ref

  trans : {A:S} -> Trans {El A} _==_
  trans {nat}{el x}{el y}{el z} (eq p) (eq q) = eq (transN p q)
  trans {pi A F pF}{el (Pair f pf)}{el (Pair g pg)}{el (Pair h ph)}
        (eq f=g)(eq g=h) = eq f=h
    where
      f=h : (x : El A) -> f x == h x
      f=h x = trans (f=g x) (g=h x)

  sym : {A:S} -> Sym {El A} _==_
  sym {nat}{el x}{el y} (eq p)  = eq (symN p)
  sym {pi A F pF}{el (Pair f pf)}{el (Pair g pg)}
        (eq f=g) = eq g=f
    where
      g=f : (x : El A) -> g x == f x
      g=f x = sym (f=g x)




