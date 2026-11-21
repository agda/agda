postulate A : Set
postulate a : A

data P (x : A) : Set where mkP : P x
data Q (x : A) : Set where mkQ : Q x

record Register (R : A → Set) : Set where
  constructor Reg
open Register

record Pointed  (R : A → Set) : Set where
  constructor Pt
  field at : R a
open Pointed {{...}}

wrap : {R : A → Set} {{_ : Register R}} {x : A} → R x → R x
wrap r = r

val : {R : A → Set} {{_ : Register R}} {{_ : Pointed R}} → R a
val = at

instance
  Register-A : Register P ; Register-A = Reg
  Register-B : Register Q ; Register-B = Reg
  Pointed-P  : Pointed P  ; Pointed-P  = Pt mkP
  Pointed-Q  : Pointed Q  ; Pointed-Q  = Pt mkQ

q : Q a
q = wrap val
