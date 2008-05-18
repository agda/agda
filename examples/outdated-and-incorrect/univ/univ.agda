{-# OPTIONS --no-positivity-check #-}

module univ where

open import Base
open import Nat

import Logic.ChainReasoning
module Chain
  {A : Set}( _==_ : A -> A -> Set)
  (refl : {x : A} -> x == x)
  (trans : {x y z : A} -> x == y -> y == z -> x == z) =
  Logic.ChainReasoning.Mono.Homogenous _==_ (\x -> refl) (\x y z -> trans)

-- mutual inductive recursive definition of S and the functions _=S_, El, eq,
-- and all the proofs on these functions

mutual

  infix 40 _==_ _=S_ _=Fam_
  infixr 80 _<<_
  infixl 80 _>>_
  infixl 150 _!_

  data S : Set where
    nat   : S
    pi    : (A : S)(F : Fam A) -> S
    sigma : (A : S)(F : Fam A) -> S

  data Fam (A : S) : Set where
    fam : (F : El A -> S) -> Map _==_ _=S_ F -> Fam A

  _=S'_ : rel S
  nat       =S' pi _ _    = False
  nat       =S' sigma _ _ = False
  pi _ _    =S' nat       = False
  pi _ _    =S' sigma _ _ = False
  sigma _ _ =S' nat       = False
  sigma _ _ =S' pi _ _    = False
  nat       =S' nat       = True
  pi A F =S' pi B G =
      (B =S A) * \ B=A -> F =Fam G >> B=A
  sigma A F =S' sigma B G =
      (A =S B) * \A=B -> F >> A=B =Fam G

  data _=S_ (A B : S) : Set where
    eqS : A =S' B -> A =S B

  El' : S -> Set
  El' nat = Nat
  El' (pi A F) = 
    ((x : El A) -> El (F ! x)) * \f ->
    {x y : El A}(x=y : x == y) -> f x == pFam F x=y << f y
  El' (sigma A F) =
    El A * \x -> El (F ! x)

  data El (A : S) : Set where
    el : El' A -> El A

  _=='_ : {A : S} -> rel (El A)
  _=='_ {nat} (el x) (el y) = x =N y
  _=='_ {pi A F} (el < f , pf >) (el < g , pg >) =
        (x : El A) -> f x == g x
  _=='_ {sigma A F} (el < x , Fx >) (el < y , Fy >) =
        x == y * \x=y -> Fx == pFam F x=y << Fy

  data _==_ {A : S}(x y : El A) : Set where
    eq : x ==' y -> x == y

  _=Fam_ : {A : S} -> rel (Fam A)
  F =Fam G = (x : El _) -> F ! x =S G ! x

  _!_ : {A : S} -> Fam A -> El A -> S
  fam F _ ! x = F x

  pFam : {A : S}(F : Fam A) -> Map _==_ _=S_ (_!_ F)
  pFam (fam F pF) = pF

  -- Families are contravariant so they cast in the other direction.
  _>>_ : {A B : S} -> Fam A -> A =S B -> Fam B
  _>>_ {A}{B} F A=B = fam G pG
    where
      G : El B -> S
      G x = F ! (A=B << x)

      pG : Map _==_ _=S_ G
      pG x=y = pFam F (p<< A=B x=y)

  pfiFam : {A B : S}(p q : A =S B)(F : Fam A) -> F >> p =Fam F >> q
  pfiFam p q F x = pFam F (pfi p q x)

  _<<_ : {A B : S} -> A =S B -> El B -> El A
  _<<_ {nat       }{pi _ _    } (eqS ()) _
  _<<_ {nat       }{sigma _ _ } (eqS ()) _
  _<<_ {pi _ _    }{nat       } (eqS ()) _
  _<<_ {pi _ _    }{sigma _ _ } (eqS ()) _
  _<<_ {sigma _ _ }{nat       } (eqS ()) _
  _<<_ {sigma _ _ }{pi _ _    } (eqS ()) _
  _<<_ {nat       }{nat       } p x = x
  _<<_ {pi A F    }{pi B G    } (eqS < B=A , F=G >) (el < g , pg >) =
    el < f , (\{x}{y} -> pf x y) >
    where
      f : (x : El A) -> El (F ! x)
      f x = F=G x << g (B=A << x)

      pf : (x y : El A)(x=y : x == y) -> f x == pFam F x=y << f y
      pf x y x=y =
        chain> F=G x << g (B=A << x)
           === F=G x << _      << g (B=A << y)     by p<< _ (pg (p<< B=A x=y))
           === pFam F x=y << F=G y << g (B=A << y) by pfi2 _ _ _ _ _
        where
          open module C = Chain _==_ (ref {_}) (trans {_})
  _<<_ {sigma A F}{sigma B G} (eqS < A=B , F=G >) (el < y , Gy >) =
    el < A=B << y , F=G y << Gy >

  p<< : {A B : S}(A=B : A =S B) -> Map _==_ _==_ (_<<_ A=B)
  p<< {nat}{nat} _ x=y = x=y
  p<< {pi A F} {pi B G} (eqS < B=A , F=G >)
        {el < f , pf >} {el < g , pg >} (eq f=g) = eq cf=cg
    where
      cf=cg : (x : El A) -> F=G x << f (B=A << x) == F=G x << g (B=A << x)
      cf=cg x = p<< (F=G x) (f=g (B=A << x))

  p<< {sigma A F}{sigma B G}(eqS < A=B , F=G >)
      {el < x , Gx >}{el < y , Gy >} (eq < x=y , Gx=Gy >) =
      eq < cx=cy , cGx=cGy >
    where
      cx=cy : A=B << x == A=B << y
      cx=cy = p<< A=B x=y

      cGx=cGy : F=G x << Gx == pFam F cx=cy << F=G y << Gy
      cGx=cGy =
        chain> F=G x        << Gx
           === F=G x        << pFam G x=y << Gy  by p<< (F=G x) Gx=Gy
           === pFam F cx=cy << F=G y      << Gy  by pfi2 _ _ _ _ Gy
        where
          open module C = Chain _==_ (ref {_}) (trans {_})

  p<< {nat        }{pi _ _   } (eqS ()) _
  p<< {nat        }{sigma _ _} (eqS ()) _
  p<< {pi _ _   }{nat        } (eqS ()) _
  p<< {pi _ _   }{sigma _ _} (eqS ()) _
  p<< {sigma _ _}{nat        } (eqS ()) _
  p<< {sigma _ _}{pi _ _   } (eqS ()) _

  refS : Refl _=S_
  refS {nat}       = eqS T
  refS {pi A F}    = eqS < refS , (\x -> symS (pFam F (ref<< x))) >
  refS {sigma A F} = eqS < refS , (\x -> pFam F (ref<< x)) >

  transS : Trans _=S_
  transS {nat       }{nat       }{pi _ _    } _ (eqS ())
  transS {nat       }{nat       }{sigma _ _ } _ (eqS ())
  transS {nat       }{pi _ _    }               (eqS ()) _
  transS {nat       }{sigma _ _ }               (eqS ()) _
  transS {pi _ _    }{nat       }               (eqS ()) _
  transS {pi _ _    }{pi _ _    }{nat       } _ (eqS ())
  transS {pi _ _    }{pi _ _    }{sigma _ _ } _ (eqS ())
  transS {pi _ _    }{sigma _ _ }               (eqS ()) _
  transS {sigma _ _ }{nat       }               (eqS ()) _
  transS {sigma _ _ }{pi _ _    }               (eqS ()) _
  transS {sigma _ _ }{sigma _ _ }{nat       } _ (eqS ())
  transS {sigma _ _ }{sigma _ _ }{pi _ _    } _ (eqS ())
  transS {nat}{nat}{nat} p q = p
  transS {pi A F}{pi B G}{pi C H}
         (eqS < B=A , F=G >) (eqS < C=B , G=H >) = eqS < C=A , F=H >
    where
      open module C = Chain _=S_ refS transS
      C=A = transS C=B B=A
      F=H : F =Fam H >> C=A
      F=H x =
        chain> F ! x
           === G ! (B=A << x)           by F=G x
           === H ! (C=B << B=A << x)    by G=H (B=A << x)
           === H ! (C=A << x)           by pFam H (sym (trans<< C=B B=A x))
  transS {sigma A F}{sigma B G}{sigma C H}
         (eqS < A=B , F=G >)(eqS < B=C , G=H >) = eqS < A=C , F=H >
    where
      open module C = Chain _=S_ refS transS
      A=C = transS A=B B=C
      F=H : F >> A=C =Fam H
      F=H x =
        chain> F ! (A=C << x)
           === F ! (A=B << B=C << x) by pFam F (trans<< A=B B=C x)
           === G ! (B=C << x)        by F=G (B=C << x)
           === H ! x                 by G=H x

  symS : Sym _=S_
  symS {nat       }{pi _ _    } (eqS ())
  symS {nat       }{sigma _ _ } (eqS ())
  symS {pi _ _    }{nat       } (eqS ())
  symS {pi _ _    }{sigma _ _ } (eqS ())
  symS {sigma _ _ }{nat       } (eqS ())
  symS {sigma _ _ }{pi _ _    } (eqS ())
  symS {nat}{nat} p                 = p
  symS {pi A F}{pi B G} (eqS < B=A , F=G >) = eqS < A=B , G=F >
    where
      open module C = Chain _=S_ refS transS
      A=B = symS B=A
      G=F : G =Fam F >> A=B
      G=F x = symS (
        chain> F ! (A=B << x)
           === G ! (B=A << A=B << x) by F=G (A=B << x)
           === G ! (refS << x)       by pFam G (casttrans B=A A=B refS x)
           === G ! x                 by pFam G (ref<< x)
        )
  symS {sigma A F}{sigma B G}(eqS < A=B , F=G >) = eqS < B=A , G=F >
    where
      open module C = Chain _=S_ refS transS
      B=A = symS A=B
      G=F : G >> B=A =Fam F
      G=F x =
        chain> G ! (B=A << x)
           === F ! (A=B << B=A << x) by symS (F=G _)
           === F ! (refS << x)       by pFam F (casttrans _ _ _ x)
           === F ! x                 by pFam F (castref _ x)

  pfi : {A B : S}(p q : A =S B)(x : El B) -> p << x == q << x
  pfi {nat       }{pi _ _    } (eqS ()) _ _
  pfi {nat       }{sigma _ _ } (eqS ()) _ _
  pfi {pi _ _    }{nat       } (eqS ()) _ _
  pfi {pi _ _    }{sigma _ _ } (eqS ()) _ _
  pfi {sigma _ _ }{nat       } (eqS ()) _ _
  pfi {sigma _ _ }{pi _ _    } (eqS ()) _ _
  pfi {nat}{nat} _ _ x = ref
  pfi {pi A F}{pi B G} (eqS < B=A1 , F=G1 >) (eqS < B=A2 , F=G2 >)
      (el < g , pg >) = eq g1=g2
    where
      g1=g2 : (x : El A) -> F=G1 x << g (B=A1 << x)
                         == F=G2 x << g (B=A2 << x)
      g1=g2 x =
        chain> F=G1 x      << g (B=A1 << x)
           === F=G1 x << _ << g (B=A2 << x) by p<< _ (pg (pfi B=A1 B=A2 x))
           === F=G2 x      << g (B=A2 << x) by casttrans _ _ _ _
        where
          open module C = Chain _==_ (ref {_}) (trans {_})
  pfi {sigma A F}{sigma B G} (eqS < A=B1 , F=G1 >) (eqS < A=B2 , F=G2 >)
      (el < y , Gy >) = eq < x1=x2 , Fx1=Fx2 >
    where
      x1=x2 : A=B1 << y == A=B2 << y
      x1=x2 = pfi A=B1 A=B2 y

      Fx1=Fx2 : F=G1 y << Gy == pFam F x1=x2 << F=G2 y << Gy
      Fx1=Fx2 = sym (casttrans _ _ _ _)

  ref<< : {A : S}(x : El A) -> refS << x == x
  ref<< {nat}       x = ref
  ref<< {sigma A F} (el < x , Fx >) = eq < ref<< x , pfi _ _ Fx >
  ref<< {pi A F   } (el < f , pf >) = eq rf=f
    where
      rf=f : (x : El A) -> _ << f (refS << x) == f x
      rf=f x =
        chain> _ << f (refS << x)
           === _ << pFam F (ref<< x) << f x by p<< _ (pf (ref<< x))
           === _ << f x                     by sym (trans<< _ _ (f x))
           === f x                          by castref _ _
        where open module C = Chain _==_ (ref {_}) (trans {_})

  trans<< : {A B C : S}(A=B : A =S B)(B=C : B =S C)(x : El C) ->
            transS A=B B=C << x == A=B << B=C << x
  trans<< {nat       }{nat       }{pi _ _    } _ (eqS ()) _
  trans<< {nat       }{nat       }{sigma _ _ } _ (eqS ()) _
  trans<< {nat       }{pi _ _    }               (eqS ()) _ _
  trans<< {nat       }{sigma _ _ }               (eqS ()) _ _
  trans<< {pi _ _    }{nat       }               (eqS ()) _ _
  trans<< {pi _ _    }{pi _ _    }{nat       } _ (eqS ()) _
  trans<< {pi _ _    }{pi _ _    }{sigma _ _ } _ (eqS ()) _
  trans<< {pi _ _    }{sigma _ _ }               (eqS ()) _ _
  trans<< {sigma _ _ }{nat       }               (eqS ()) _ _
  trans<< {sigma _ _ }{pi _ _    }               (eqS ()) _ _
  trans<< {sigma _ _ }{sigma _ _ }{nat       } _ (eqS ()) _
  trans<< {sigma _ _ }{sigma _ _ }{pi _ _    } _ (eqS ()) _
  trans<< {nat}{nat}{nat} _ _ _ = ref
  trans<< {pi A F}{pi B G}{pi C H}
          (eqS < B=A , F=G >)(eqS < C=B , G=H >)
          (el < h , ph >) = eq prf
    where
      C=A = transS C=B B=A
      prf : (x : El A) -> _
      prf x =
        chain> _ << h (C=A << x)
           === _ << _ << h (C=B << B=A << x)     by p<< _ (ph (trans<< _ _ x))
           === F=G x << G=H _ << h (_ << _ << x) by pfi2 _ _ _ _ _
        where open module C' = Chain _==_ (ref {_}) (trans {_})
  trans<< {sigma A F}{sigma B G}{sigma C H}
          (eqS < A=B , F=G >)(eqS < B=C , G=H >)
          (el < z , Hz >) = eq < trans<< A=B B=C z , prf >
    where
      prf =
        chain> _ << Hz
           === _ << Hz                   by pfi _ _ _
           === _ << _ << Hz              by trans<< _ _ _
           === _ << F=G _ << G=H z << Hz by trans<< _ _ _
        where open module C' = Chain _==_ (ref {_}) (trans {_})

  -- we never need this one, but it feels like it should be here...
  sym<< : {A B : S}(A=B : A =S B)(x : El B) ->
          symS A=B << A=B << x == x
  sym<< A=B x =
    chain> symS A=B << A=B << x
       === refS << x       by casttrans _ _ _ x
       === x               by ref<< x
    where open module C' = Chain _==_ (ref {_}) (trans {_})

  castref : {A : S}(p : A =S A)(x : El A) -> p << x == x
  castref A=A x =
    chain> A=A << x
       === refS << x  by pfi A=A refS x
       === x          by ref<< x
    where open module C = Chain _==_ (ref {_}) (trans {_})

  casttrans : {A B C : S}(A=B : A =S B)(B=C : B =S C)(A=C : A =S C)(x : El C) ->
               A=B << B=C << x == A=C << x
  casttrans A=B B=C A=C x =
    chain> A=B << B=C << x
       === _ << x     by sym (trans<< _ _ _)
       === A=C << x   by pfi _ _ _
    where open module C' = Chain _==_ (ref {_}) (trans {_})

  pfi2 : {A B1 B2 C : S}
         (A=B1 : A =S B1)(A=B2 : A =S B2)(B1=C : B1 =S C)(B2=C : B2 =S C)
         (x : El C) -> A=B1 << B1=C << x == A=B2 << B2=C << x
  pfi2 A=B1 A=B2 B1=C B2=C x =
    chain> A=B1 << B1=C << x
       === _ << x             by casttrans _ _ _ x
       === A=B2 << B2=C << x  by trans<< _ _ x
    where
      open module C = Chain _==_ (ref {_}) (trans {_})

  ref : {A : S} -> Refl {El A} _==_
  ref {nat}       {el n}          = eq (refN {n})
  ref {pi A F}    {el < f , pf >} = eq \x -> ref
  ref {sigma A F} {el < x , Fx >} = eq < ref , sym (castref _ _) >

  trans : {A : S} -> Trans {El A} _==_
  trans {nat}{el x}{el y}{el z} (eq p) (eq q) = eq (transN {x}{y}{z} p q)
  trans {pi A F}{el < f , pf >}{el < g , pg >}{el < h , ph >}
        (eq f=g)(eq g=h) = eq \x -> trans (f=g x) (g=h x)
  trans {sigma A F}{el < x , Fx >}{el < y , Fy >}{el < z , Fz >}
        (eq < x=y , Fx=Fy >)(eq < y=z , Fy=Fz >) =
        eq < x=z , Fx=Fz >
    where
      x=z   = trans x=y y=z
      Fx=Fz =
        chain> Fx
           === pFam F x=y << Fy               by Fx=Fy
           === pFam F x=y << pFam F y=z << Fz by p<< _ Fy=Fz
           === pFam F x=z << Fz               by casttrans _ _ _ _
        where open module C = Chain _==_ (ref {_}) (trans {_})

  sym : {A : S} -> Sym {El A} _==_
  sym {nat}{el x}{el y} (eq p)  = eq (symN {x}{y} p)
  sym {pi A F}{el < f , pf >}{el < g , pg >}
      (eq f=g) = eq \x -> sym (f=g x)
  sym {sigma A F}{el < x , Fx >}{el < y , Fy >}
      (eq < x=y , Fx=Fy >) = eq < y=x , Fy=Fx >
    where
      y=x = sym x=y
      Fy=Fx = sym (
        chain> pFam F y=x << Fx 
           === pFam F y=x << pFam F x=y << Fy by p<< (pFam F y=x) Fx=Fy
           === refS << Fy                     by casttrans _ _ _ _
           === Fy                             by castref _ _
        )
        where open module C = Chain _==_ (ref {_}) (trans {_})

refFam : {A : S} -> Refl (_=Fam_ {A})
refFam x = refS

transFam : {A : S} -> Trans (_=Fam_ {A})
transFam F=G G=H x = transS (F=G x) (G=H x)

symFam : {A : S} -> Sym (_=Fam_ {A})
symFam F=G x = symS (F=G x)

castref2 : {A B : S}(A=B : A =S B)(B=A : B =S A)(x : El A) ->
           A=B << B=A << x == x
castref2 A=B B=A x = trans (casttrans A=B B=A refS x) (ref<< x)

