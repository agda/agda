module Nom where

open import Basics
open import Pr

data Nom : Set where
  Ze : Nom
  Su : Nom -> Nom
  Pu : Nom -> Nom

_NomQ_ : Nom -> Nom -> Pr
Ze NomQ Ze = tt
Ze NomQ (Su y) = ff
Ze NomQ (Pu y) = ff
(Su x) NomQ Ze = ff
(Su x) NomQ (Su y) = x eq y
(Su x) NomQ (Pu y) = ff
(Pu x) NomQ Ze = ff
(Pu x) NomQ (Su y) = ff
(Pu x) NomQ (Pu y) = x eq y

nomQ : {x y : Nom} -> [| (x eq y) => (x NomQ y) |]
nomQ {Ze} refl = _
nomQ {Su x} refl = refl
nomQ {Pu x} refl = refl

nomEq : (x y : Nom) -> Decision (x eq y)
nomEq Ze Ze = yes refl
nomEq Ze (Su y) = no nomQ
nomEq Ze (Pu y) = no nomQ 
nomEq (Su x) Ze = no nomQ
nomEq (Su x) (Su y) with nomEq x y
nomEq (Su x) (Su .x) | yes refl = yes refl
nomEq (Su x) (Su y) | no p = no (p o nomQ)
nomEq (Su x) (Pu y) = no nomQ
nomEq (Pu x) Ze = no nomQ
nomEq (Pu x) (Su y) = no nomQ
nomEq (Pu x) (Pu y) with nomEq x y
nomEq (Pu x) (Pu .x) | yes refl = yes refl
nomEq (Pu x) (Pu y)  | no p = no (p o nomQ)

data Nat : Set where
  ze : Nat
  su : Nat -> Nat

pfog : Nom -> Nat
pfog Ze = ze
pfog (Su x) = pfog x
pfog (Pu x) = su (pfog x)

NatGE : Nat -> Nat -> Bool
NatGE ze _ = false
NatGE (su _) ze = true
NatGE (su x) (su y) = NatGE x y

_>_ : Nat -> Nat -> Pr
x > y = So (NatGE x y)

_>?_ : (x y : Nat) -> Decision (x > y)
x >? y = so (NatGE x y)

_P>_ : Nom -> Nom -> Pr
x P> y = pfog x > pfog y

_S+_ : Nat -> Nom -> Nom
ze S+ y = y
su x S+ y = Su (x S+ y)

PSlem : (n : Nat)(x : Nom) -> Id (pfog (n S+ x)) (pfog x)
PSlem ze x = refl
PSlem (su n) x = PSlem n x

Plem : (x y : Nom) -> [| x P> y |] -> [| Pu x P> y |]
Plem _ Ze p = _
Plem x (Su y) p = Plem x y p
Plem Ze (Pu y) ()
Plem (Su x) (Pu y) p = Plem x (Pu y) p
Plem (Pu x) (Pu y) p = Plem x y p

asym : (x : Nom) -> [| ∼ (x P> x) |]
asym Ze ()
asym (Su x) p = asym x p
asym (Pu x) p = asym x p

record Nominal (X : Set) : Set1 where
  field
    Everywhere  : Pow Nom -> Pow X
    everywhere  : (P Q : Pow Nom) -> [| P ==> Q |] ->
                  [| Everywhere P ==> Everywhere Q |]
