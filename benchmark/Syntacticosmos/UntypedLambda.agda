module UntypedLambda where

open import Basics
open import Pr
open import Nom
import Syntacticosmos

data Tag : Set where
  lamT : Tag
  appT : Tag

open module ULam = Syntacticosmos TT TT (\_ -> Tag)

LAM : Kind
LAM = Ty _

SigLAM : Kind
SigLAM = Pi _ conk where
  conk : Tag -> Kind
  conk lamT = (LAM |> LAM) |> LAM
  conk appT = LAM |> LAM |> LAM

Lam : Cxt -> Set
Lam G = G [! SigLAM !]- LAM

lam : {G : Cxt}(x : Nom){Gx : [| G Hasn't x |]} ->
      Lam ((G [ x - LAM ]) {Gx}) -> Lam G
lam x {Gx} b = G[ lamT G^ G\\ (bind x {Gx} b) G& Gnil ]

app : {G : Cxt} -> Lam G -> Lam G -> Lam G
app f s = G[ appT G^ f G& s G& Gnil ]

moo : Lam EC
moo = lam Ze (lam (Su Ze) (var Ze))

noo : Lam EC
noo = lam (Su Ze) (lam Ze (var (Su Ze)))

coo : Id moo noo
coo = refl



