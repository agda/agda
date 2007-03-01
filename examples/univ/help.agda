
module help where

open import univ
open import Base

-- Prelims
infixl 150 _#_

K : {A : S} -> S -> Fam A
K B = fam (\_ -> B) (\_ -> refS)

_#_ : {A : S}{F : Fam A} -> El (pi A F) -> (x : El A) -> El (F ! x)
el < f , _ > # x = f x

pFun : {A : S}{F : Fam A}(f : El (pi A F)){x y : El A}(x=y : x == y) ->
       f # x == pFam F x=y << f # y
pFun (el < f , pf >) x=y = pf x=y

p# : {A : S}{F : Fam A}{f g : El (pi A F)}{x : El A} -> f == g -> f # x == g # x
p# {A}{F}{el < f , _ >}{el < g , _ >} (eq f=g) = f=g _

eqDom : {A B : S}{F : Fam A}{G : Fam B} ->
        pi A F =S pi B G -> B =S A
eqDom (eqS < B=A , _ >) = B=A

eqCod : {A B : S}{F : Fam A}{G : Fam B} ->
        (AF=BG : pi A F =S pi B G)(x : El A) ->
        F ! x =S G ! (eqDom AF=BG << x)
eqCod (eqS < B=A , F=G >) = F=G

distr<<# : {A B : S}{F : Fam A}{G : Fam B}(f : El (pi A F)){x : El B}
            (BG=AF : pi B G =S pi A F) ->
            (BG=AF << f) # x == eqCod BG=AF x << f # (eqDom BG=AF << x)
distr<<# (el < f , pf >) {x} (eqS < A=B , G=F >) = ref

eqSnd : {A : S}{F : Fam A}{x : El A}{y z : El (F ! x)} ->
        y == z -> _==_ {sigma A F} (el < x , y >) (el < x , z >)
eqSnd {A}{F}{x}{y}{z} y=z = eq < ref , y=cz >
  where
    y=cz : y == pFam F ref << z
    y=cz = trans y=z (sym (castref _ _))

IsFun : {A : S}{F : Fam A}(f : (x : El A) -> El (F ! x)) -> Set
IsFun {A}{F} f = {x y : El A}(p : F ! x =S F ! y)(x=y : x == y) ->
                 f x == p << f y

mkFun : {A : S}{F : Fam A}(f : (x : El A) -> El (F ! x)) ->
        IsFun {A}{F} f -> El (pi A F)
mkFun {A}{F} f pf = el < f , (\{x}{y} x=y -> pf (pFam F x=y) x=y) >

curryFam : {A : S}{F : Fam A} -> Fam (sigma A F) -> (x : El A) -> Fam (F ! x)
curryFam {A}{F} G x = fam H pH
  where
    H : El (F ! x) -> S
    H y = G ! el < x , y >

    pH : Map _==_ _=S_ H
    pH y=z = pFam G (eq < ref , trans y=z (sym (castref _ _)) >)

