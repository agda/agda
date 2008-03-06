module Cxt (K : Set) where

open import Basics
open import Pr
open import Nom

mutual
  data Cxt : Set where
    EC : Cxt
    _[_-_] : (G : Cxt)(x : Nom) -> K -> {p : [| G Hasn't x |]} -> Cxt

  HAS : Cxt -> Nom -> Bool
  HAS EC x = false
  HAS (G [ y - S ]) x with nomEq y x
  HAS (G [ y - S ]) .y   | yes refl = true
  ...                    | no n = HAS G x

  _Has_ : Cxt -> Nom -> Pr
  G Has x = So (HAS G x)

  _Hasn't_ : Cxt -> Nom -> Pr
  G Hasn't x = So (not (HAS G x))

GooN : (G : Cxt)(T : K) -> Nom -> Pr
GooN EC T y = ff
GooN (G [ x - S ]) T y with nomEq x y
GooN (G [ x - S ]) T .x   | yes refl   = S eq T
GooN (G [ x - S ]) T y    | no n       = GooN G T y

_?-_ : (G : Cxt)(x : Nom){p : [| G Has x |]} -> K :- \ T -> GooN G T x
(EC ?- y) {}
(G [ x - S ]) ?- y       with nomEq x y
(G [ x - S ]) ?- .x         | yes refl  = [ S / refl ]
((G [ x - S ]) ?- y) {p}    | no n      = (G ?- y) {p}

topGooN : (G : Cxt)(x : Nom){p : [| G Hasn't x |]}(S : K) ->
          [| GooN ((G [ x - S ]) {p}) S x |]
topGooN G x S with nomEq x x 
topGooN G x S | yes refl  = refl
topGooN G x S | no n      = magic (n refl)

