module Pr where

data FF : Set where

magic : {X : Set} -> FF -> X
magic ()

record TT : Set where

data Id {S : Set}(s : S) : S -> Set where
  refl : Id s s

data Pr : Set1 where
  tt : Pr
  ff : Pr
  _/\_ : Pr -> Pr -> Pr
  all : (S : Set) -> (S -> Pr) -> Pr
  _eq_ : {S : Set} -> S -> S -> Pr

record Sig (S : Set)(T : S -> Set) : Set where
  field
    fst : S
    snd : T fst

open module Sig' {S : Set}{T : S -> Set} = Sig {S}{T} public

_,_ : {S : Set}{T : S -> Set}(s : S) -> T s -> Sig S T
s , t = record {fst = s ; snd = t}

[|_|] : Pr -> Set
[| tt |] = TT
[| ff |] = FF
[| P /\ Q |] = Sig [| P |] \_ -> [| Q |]
[| all S P |] = (x : S) -> [| P x |]
[| a eq b |] = Id a b

_=>_ : Pr -> Pr -> Pr
P => Q = all [| P |] \_ -> Q

∼ : Pr -> Pr
∼ P = P => ff

data Decision (P : Pr) : Set where
  yes  : [| P |]   -> Decision P
  no   : [| ∼ P |] -> Decision P

data Bool : Set where
  true : Bool
  false : Bool

So : Bool -> Pr
So true = tt
So false = ff

not : Bool -> Bool
not true = false
not false = true

so : (b : Bool) -> Decision (So b)
so true = yes _
so false = no magic

potahto : (b : Bool) -> [| So (not b) => ∼ (So b) |]
potahto true () _
potahto false _ ()

PEx : (P : Pr) -> ([| P |] -> Pr) -> Pr
PEx P Q = P /\ all [| P |] Q

Pow : Set -> Set1
Pow X = X -> Pr

_==>_ : {X : Set} -> Pow X -> Pow X -> Pr
_==>_ {X} P Q = all X \x -> P x => Q x

Decidable : {X : Set}(P : Pow X) -> Set
Decidable {X} P = (x : X) -> Decision (P x)

data _:-_ (S : Set)(P : Pow S) : Set where
  [_/_] : (s : S) -> [| P s |] -> S :- P

wit : {S : Set}{P : S -> Pr} -> S :- P -> S
wit [ s / p ] = s

cert : {S : Set}{P : S -> Pr}(sp : S :- P) -> [| P (wit sp) |]
cert [ s / p ] = p

_??_ : {S : Set}{P : S -> Pr}
      (sp : S :- P){M : Set} ->
      ((s : S)(p : [| P s |]) -> M) ->
      M
sp ?? m = m (wit sp) (cert sp)
