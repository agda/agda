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

infix 20 _*_

data _*_ (A:Set)(B : A -> Set) : Set where
 <_,_> : (x:A) -> B x -> A * B

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
    nat   : S
    pi    : (A : S)(F : El A -> S) -> Map (El A) _==_ S _=S_ F -> S
    sigma : (A : S)(F : El A -> S) -> Map (El A) _==_ S _=S_ F -> S

  _=S'_ : rel S
  nat          =S' nat          = N1
  nat          =S' pi _ _ _     = N0
  pi _ _ _     =S' nat          = N0
  nat          =S' sigma _ _ _  = N0
  sigma _ _ _  =S' nat          = N0
  sigma _ _ _  =S' pi _ _ _     = N0
  pi _ _ _     =S' sigma _ _ _  = N0
  pi A F pF    =S' pi B G pG    =
      (B =S A) * \ B=A -> (x : El A) -> F x =S G (B=A << x)
  sigma A F pF =S' sigma B G pG =
      (A =S B) * \A=B -> (x : El B) -> F (A=B << x) =S G x

  data _=S_ (A B : S) : Set where
    eqS : A =S' B -> A =S B

  El' : S -> Set
  El' nat = N
  El' (pi A F pF) = 
    ((x : El A) -> El (F x)) * \f ->
    {x y : El A}(x=y : x == y) -> f x == pF x=y << f y
  El' (sigma A F pF) =
    El A * \x -> El (F x)

  data El (A : S) : Set where
    el : El' A -> El A

  _=='_ : {A : S} -> rel (El A)
  _=='_ {nat} (el x) (el y) = x =N y
  _=='_ {pi A F pF} (el < f , pf >) (el < g , pg >) =
        (x : El A) -> f x == g x
  _=='_ {sigma A F pF} (el < x , Fx >) (el < y , Fy >) =
        x == y * \x=y -> Fx == pF x=y << Fy

  data _==_ {A : S}(x y : El A) : Set where
    eq : x ==' y -> x == y

  _<<_ : {A B : S} -> A =S B -> El B -> El A
  _<<_ {nat        }{pi _ _ _   } (eqS ()) _
  _<<_ {nat        }{sigma _ _ _} (eqS ()) _
  _<<_ {pi _ _ _   }{nat        } (eqS ()) _
  _<<_ {pi _ _ _   }{sigma _ _ _} (eqS ()) _
  _<<_ {sigma _ _ _}{nat        } (eqS ()) _
  _<<_ {sigma _ _ _}{pi _ _ _   } (eqS ()) _
  _<<_ {nat        }{nat        } p x = x
  _<<_ {pi A F pF  }{pi B G pG  } (eqS < B=A , F=G >) (el < g , pg >) =
    el < f , (\{x}{y} -> pf x y) >
    where
      f : (x : El A) -> El (F x)
      f x = F=G x << g (B=A << x)

      pf : (x y : El A)(x=y : x == y) -> f x == pF x=y << f y
      pf x y x=y =
        chain> F=G x << g (B=A << x)
           === F=G x << _      << g (B=A << y)  by p<< _ (pg (p<< B=A x=y))
           === Fx=Gcx          << g (B=A << y)  by casttrans _ _ _ _
           === pF x=y << F=G y << g (B=A << y)  by sym (casttrans _ _ _ _)
        where
          open module C = Chain _==_ (ref {F x}) (trans {F x})
          Fx=Gcx = transS (pF x=y) (F=G y)
  _<<_ {sigma A F pF}{sigma B G pG} (eqS < A=B , F=G >) (el < y , Gy >) =
    el < A=B << y , F=G y << Gy >

  p<< : {A B : S}(A=B : A =S B) -> Map (El B) _==_ (El A) _==_ (_<<_ A=B)
  p<< {nat}{nat} _ x=y = x=y
  p<< {pi A F pF} {pi B G pG} (eqS < B=A , F=G >)
        {el < f , pf >} {el < g , pg >} (eq f=g) = eq cf=cg
    where
      cf=cg : (x : El A) -> F=G x << f (B=A << x) == F=G x << g (B=A << x)
      cf=cg x = p<< (F=G x) (f=g (B=A << x))

  p<< {sigma A F pF}{sigma B G pG}(eqS < A=B , F=G >)
      {el < x , Gx >}{el < y , Gy >} (eq < x=y , Gx=Gy >) = eq < cx=cy , cGx=cGy >
    where
      cx=cy : A=B << x == A=B << y
      cx=cy = p<< A=B x=y

      cGx=cGy : F=G x << Gx == pF cx=cy << F=G y << Gy
      cGx=cGy =
        chain> F=G x    << Gx
           === F=G x    << pG x=y << Gy  by p<< (F=G x) Gx=Gy
           === Fcx=Gy             << Gy  by casttrans _ _ _ _
           === pF cx=cy << F=G y  << Gy  by sym (casttrans _ _ _ _)
        where
          open module C = Chain _==_ (ref {F (A=B << x)}) (trans {F (A=B << x)})
          Fcx=Gy = transS (F=G x) (pG x=y)

  p<< {nat        }{pi _ _ _   } (eqS ()) _
  p<< {nat        }{sigma _ _ _} (eqS ()) _
  p<< {pi _ _ _   }{nat        } (eqS ()) _
  p<< {pi _ _ _   }{sigma _ _ _} (eqS ()) _
  p<< {sigma _ _ _}{nat        } (eqS ()) _
  p<< {sigma _ _ _}{pi _ _ _   } (eqS ()) _

  refS : Refl _=S_
  refS {nat}          = eqS T
  refS {pi A F pF}    = eqS < refS , (\(x : El A) -> symS (pF (castref refS x))) >
  refS {sigma A F pF} = eqS < refS , (\(x : El A) -> pF (castref refS x)) >

  transS : Trans _=S_
  transS {nat         }{nat         }{pi _ _ _    } _ (eqS ())
  transS {nat         }{nat         }{sigma _ _ _ } _ (eqS ())
  transS {nat         }{pi _ _ _    }               (eqS ()) _
  transS {nat         }{sigma _ _ _ }               (eqS ()) _
  transS {pi _ _ _    }{nat         }               (eqS ()) _
  transS {pi _ _ _    }{pi _ _ _    }{nat         } _ (eqS ())
  transS {pi _ _ _    }{pi _ _ _    }{sigma _ _ _ } _ (eqS ())
  transS {pi _ _ _    }{sigma _ _ _ }               (eqS ()) _
  transS {sigma _ _ _ }{nat         }               (eqS ()) _
  transS {sigma _ _ _ }{pi _ _ _    }               (eqS ()) _
  transS {sigma _ _ _ }{sigma _ _ _ }{nat         } _ (eqS ())
  transS {sigma _ _ _ }{sigma _ _ _ }{pi _ _ _    } _ (eqS ())
  transS {nat}{nat}{nat} p q = p
  transS {pi A F pF}{pi B G pG}{pi C H pH}
         (eqS < B=A , F=G >) (eqS < C=B , G=H >) = eqS < C=A , F=H >
    where
      open module C = Chain _=S_ refS transS
      C=A = transS C=B B=A
      F=H : (x : El A) -> F x =S H (C=A << x)
      F=H x =
        chain> F x
           === G (B=A << x)           by F=G x
           === H (C=B << B=A << x)    by G=H (B=A << x)
           === H (C=A << x)           by pH (casttrans C=B B=A C=A x)
  transS {sigma A F pF}{sigma B G pG}{sigma C H pH}
         (eqS < A=B , F=G >)(eqS < B=C , G=H >) = eqS < A=C , F=H >
    where
      open module C = Chain _=S_ refS transS
      A=C = transS A=B B=C
      F=H : (x : El C) -> F (A=C << x) =S H x
      F=H x =
        chain> F (A=C << x)
           === F (A=B << B=C << x) by pF (sym (casttrans A=B B=C A=C x))
           === G (B=C << x)        by F=G (B=C << x)
           === H x                 by G=H x

  symS : Sym _=S_
  symS {nat        }{pi _ _ _   } (eqS ())
  symS {nat        }{sigma _ _ _} (eqS ())
  symS {pi _ _ _   }{nat        } (eqS ())
  symS {pi _ _ _   }{sigma _ _ _} (eqS ())
  symS {sigma _ _ _}{nat        } (eqS ())
  symS {sigma _ _ _}{pi _ _ _   } (eqS ())
  symS {nat}{nat} p                 = p
  symS {pi A F pF}{pi B G pG} (eqS < B=A , F=G >) = eqS < A=B , G=F >
    where
      open module C = Chain _=S_ refS transS
      A=B = symS B=A
      G=F : (x : El B) -> G x =S F (A=B << x)
      G=F x =
        chain> G x
           === G (refS << x)        by symS (pG (castref refS x))
           === G (B=A << A=B << x)  by symS (pG (casttrans B=A A=B refS x))
           === F (A=B << x)         by symS (F=G (A=B << x))
  symS {sigma A F pF}{sigma B G pG}(eqS < A=B , F=G >) = eqS < B=A , G=F >
    where
      open module C = Chain _=S_ refS transS
      B=A = symS A=B
      G=F : (x : El A) -> G (B=A << x) =S F x
      G=F x =
        chain> G (B=A << x)
           === F (A=B << B=A << x) by symS (F=G _)
           === F (refS << x)       by pF (casttrans _ _ _ x)
           === F x                 by pF (castref _ x)

  pfi : {A B : S}(p q : A =S B)(x : El B) -> p << x == q << x
  pfi {nat}{nat} _ _ x = ref
  pfi {nat}{pi _ _ _} (eqS ()) _ _
  pfi {pi _ _ _}{nat} (eqS ()) _ _
  pfi {pi A F pF}{pi B G pG} (eqS < B=A1 , F=G1 >) (eqS < B=A2 , F=G2 >)
      (el < g , pg >) = eq g1=g2
    where
      g1=g2 : (x : El A) -> F=G1 x << g (B=A1 << x)
                         == F=G2 x << g (B=A2 << x)
      g1=g2 x =
        chain> F=G1 x      << g (B=A1 << x)
           === F=G1 x << _ << g (B=A2 << x) by p<< (F=G1 x) (pg (pfi B=A1 B=A2 x))
           === F=G2 x      << g (B=A2 << x) by casttrans (F=G1 x) _ (F=G2 x) _
        where
          open module C = Chain _==_ (ref {F x}) (trans {F x})

  castref : {A : S}(p : A =S A)(x : El A) -> p << x == x
  castref {nat} p x = ref
  castref {pi A F pF} (eqS < A=A , F=F >) (el < f , pf >) = eq cf=f
    where
      cf=f : (x : El A) -> F=F x << f (A=A << x) == f x
      cf=f x =
        chain> F=F x << f (A=A << x)
           === F=F x << Fcx=Fx << f x by p<< (F=F x) (pf (castref A=A x))
           === refS << f x            by casttrans _ _ _ (f x)
           === f x                    by castref _ (f x)
        where
          open module C = Chain _==_ (ref {F x}) (trans {F x})
          Fcx=Fx = _

  casttrans : {A B C : S}(A=B : A =S B)(B=C : B =S C)(A=C : A =S C)(x : El C) ->
               A=B << B=C << x == A=C << x
  casttrans {nat}{nat}{nat} _ _ _ x = ref
  casttrans {nat}{nat}{pi _ _ _}      _      (eqS ()) _ _
  casttrans {nat}{pi _ _ _}{_}       (eqS ()) _ _ _
  casttrans {pi _ _ _}{nat}{_}       (eqS ()) _ _ _
  casttrans {pi _ _ _}{pi _ _ _}{nat} _      (eqS ()) _ _
  casttrans {pi A F pF}{pi B G pG}{pi C H pH}
            (eqS < B=A , F=G >)(eqS < C=B , G=H >)(eqS < C=A , F=H >)
            (el < h , ph >) = eq prf
    where
      prf : (x : El A) -> _ << _ << h (C=B << B=A << x) == _ << h (C=A << x)
      prf x =
        chain> F=G x   << G=H _ << h (C=B << B=A << x)
           === Fx=Hccx          << h (C=B << B=A << x) by casttrans _ _ _ _
           === Fx=Hccx << _     << h (C=A << x)        by p<< _ (ph (casttrans C=B B=A C=A x))
           === F=H x            << h (C=A << x)        by casttrans _ _ _ _
        where
          Fx=Hccx  = transS (F=G x) (G=H _)
          open module C = Chain _==_ (ref {F x}) (trans {F x})

  ref : {A:S} -> Refl {El A} _==_
  ref {nat}      {el n}          = eq refN
  ref {pi A F pF}{el < f , pf >} = eq \x -> ref

  trans : {A:S} -> Trans {El A} _==_
  trans {nat}{el x}{el y}{el z} (eq p) (eq q) = eq (transN p q)
  trans {pi A F pF}{el < f , pf >}{el < g , pg >}{el < h , ph >}
        (eq f=g)(eq g=h) = eq \x -> trans (f=g x) (g=h x)

  sym : {A:S} -> Sym {El A} _==_
  sym {nat}{el x}{el y} (eq p)  = eq (symN p)
  sym {pi A F pF}{el < f , pf >}{el < g , pg >}
      (eq f=g) = eq \x -> sym (f=g x)

