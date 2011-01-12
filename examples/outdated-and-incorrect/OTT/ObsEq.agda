module ObsEq where

data Zero : Set where

record One : Set where

data Two : Set where
  tt : Two
  ff : Two

Π : (S : Set)(T : S -> Set) -> Set
Π S T = (x : S) -> T x

record Σ (S : Set)(T : S -> Set) : Set where
  field
    fst : S
    snd : T fst

_,_ : {S : Set}{T : S -> Set}(s : S) -> T s -> Σ S T
s , t = record {fst = s; snd = t}

open module Σ' {S : Set}{T : S -> Set} = Σ {S} {T}

data W (S : Set)(T : S -> Set) : Set where
  _<|_ : (s : S) -> (T s -> W S T) -> W S T


mutual

  data ∗ : Set where
    /0/ : ∗
    /1/ : ∗
    /2/ : ∗
    /Π/ : (S : ∗)(T : [ S ] -> ∗) -> ∗
    /Σ/ : (S : ∗)(T : [ S ] -> ∗) -> ∗
    /W/ : (S : ∗)(T : [ S ] -> ∗) -> ∗

  [_] : ∗ -> Set
  [ /0/ ]      = Zero
  [ /1/ ]      = One
  [ /2/ ]      = Two
  [ /Π/ S T ]  = Π [ S ] \s -> [ T s ]
  [ /Σ/ S T ]  = Σ [ S ] \s -> [ T s ]
  [ /W/ S T ]  = W [ S ] \s -> [ T s ]

infixr 40 _⟶_

_⟶_ : ∗ -> ∗ -> ∗
S ⟶ T = /Π/ S \_ -> T

{-
_Ψ_ : Zero -> (S : ∗) -> [ S ]
() Ψ S   -- magic as there's no such thing
-}

_Ψ : Zero -> {S : Set} -> S
() Ψ

Case : Two -> ∗ -> ∗ -> ∗
Case tt St Sf = St
Case ff St Sf = Sf

case : (P : Two -> ∗)(b : Two) -> [ P tt ] -> [ P ff ] -> [ P b ]
case P tt ptt pff = ptt
case P ff ptt pff = pff

rec : {S : Set}{T : S -> Set}(P : W S T -> ∗)(x : W S T) ->
      ((s : S)(f : T s -> W S T) ->
       ((t : T s) -> [ P (f t) ]) -> [ P (s <| f) ]) ->
      [ P x ]
rec P (s <| f) p = p s f \t -> rec P (f t) p


/Nat/ : ∗
/Nat/ = /W/ /2/ \b -> Case b /0/ /1/

zero : [ /Nat/ ]
zero = tt <| \z -> z Ψ

suc : [ /Nat/ ⟶ /Nat/ ]
suc n = ff <| \_ -> n

{-
elimNatSet : (P : [ /Nat/ ] -> Set) ->
          P zero ->
          ((k : [ /Nat/ ]) -> P k -> P (suc k)) ->
          (n : [ /Nat/ ]) -> P n
elimNatSet P pz ps (tt <| g) = {! !}
elimNatSet P pz ps (ff <| g) = {! !}
-}

infixr 60 _∧_

data † : Set where
  ⊥   : †
  TT  : †
  _∧_ : † -> † -> †
  ∏   : (S : ∗) -> ([ S ] -> †) -> †

|- : † -> ∗
|- ⊥       = /0/
|- TT      = /1/
|- (P ∧ Q) = /Σ/ (|- P) \_ -> |- Q
|- (∏ S P) = /Π/ S \s -> |- (P s)

Prf : † -> Set
Prf P = [ |- P ]

infixr 40 _⇒_

_⇒_ : † -> † -> †
P ⇒ Q = ∏ (|- P) \_ -> Q

infix 80 _⇔_

mutual

  _⇔_ : ∗ -> ∗ -> †
  /0/        ⇔  /0/        =  TT
  /1/        ⇔  /1/        =  TT
  /2/        ⇔  /2/        =  TT
  /Π/ S0 T0  ⇔  /Π/ S1 T1  =
    S1 ⇔ S0  ∧
    ∏ S1 \s1 -> ∏ S0 \s0 -> (S1 > s1 ≅ S0 > s0) ⇒ (T0 s0 ⇔ T1 s1)
  /Σ/ S0 T0  ⇔  /Σ/ S1 T1  =
    S0 ⇔ S1  ∧
    ∏ S0 \s0 -> ∏ S1 \s1 -> (S0 > s0 ≅ S1 > s1) ⇒ (T0 s0 ⇔ T1 s1)
  /W/ S0 T0  ⇔  /W/ S1 T1  =
    S0 ⇔ S1  ∧
    ∏ S0 \s0 -> ∏ S1 \s1 -> (S0 > s0 ≅ S1 > s1) ⇒ (T1 s1 ⇔ T0 s0)
  _          ⇔  _ = ⊥

  _>_≅_>_ : (S : ∗) -> [ S ] -> (T : ∗) -> [ T ] -> †
  /0/ > _  ≅ /0/ > _  = TT
  /1/ > _  ≅ /1/ > _  = TT
  /2/ > tt ≅ /2/ > tt = TT
  /2/ > ff ≅ /2/ > ff = TT

  /Π/ S0 T0 > f0 ≅ /Π/ S1 T1 > f1 =
    ∏ S0 \s0 -> ∏ S1 \s1 -> (S0 > s0 ≅ S1 > s1) ⇒
      (T0 s0 > f0 s0 ≅ T1 s1 > f1 s1)

  /Σ/ S0 T0 > p0 ≅ /Σ/ S1 T1 > p1 =
    (S0          > fst p0 ≅ S1          > fst p1) ∧
    (T0 (fst p0) > snd p0 ≅ T1 (fst p1) > snd p1)

  /W/ S0 T0 > (s0 <| f0) ≅ /W/ S1 T1 > (s1 <| f1) =
    (S0 > s0 ≅ S1 > s1)  ∧
    ∏ (T0 s0) \t0 -> ∏ (T1 s1) \t1 ->
       (T0 s0 > t0 ≅ T1 s1 > t1) ⇒
       (/W/ S0 T0 > f0 t0 ≅ /W/ S1 T1 > f1 t1)

  _ > _ ≅ _ > _ = ⊥

mutual

  _>_<_!_ : (S : ∗) -> [ S ] -> (T : ∗) -> Prf (S ⇔ T) -> [ T ]

  /0/ > z < /0/ ! _  = z
  /1/ > u < /1/ ! _  = u
  /2/ > b < /2/ ! _  = b

  /Π/ S0 T0 > f0 < /Π/ S1 T1 ! Q =
    let S1S0 : Prf (S1 ⇔ S0)
        S1S0 = fst Q
        T0T1 : Prf (∏ S1 \s1 -> ∏ S0 \s0 -> (S1 > s1 ≅ S0 > s0) ⇒
                      (T0 s0 ⇔ T1 s1))
        T0T1 = snd Q
    in  \s1 ->
        let s0   : [ S0 ]
            s0   = S1 > s1 < S0 ! S1S0
            s1s0 : Prf (S1 > s1 ≅ S0 > s0)
            s1s0 = [| S1 > s1 < S0 ! S1S0 |]
        in  T0 s0 > f0 s0 < T1 s1 ! T0T1 s1 s0 s1s0

  /Σ/ S0 T0 > p0 < /Σ/ S1 T1 ! Q =
    let S0S1 : Prf (S0 ⇔ S1)
        S0S1 = fst Q
        T0T1 : Prf (∏ S0 \s0 -> ∏ S1 \s1 -> (S0 > s0 ≅ S1 > s1) ⇒
                      (T0 s0 ⇔ T1 s1))
        T0T1 = snd Q
        s0   : [ S0 ]
        s0   = fst p0
        s1   : [ S1 ]
        s1   = S0 > s0 < S1 ! S0S1
        s0s1 : Prf (S0 > s0 ≅ S1 > s1)
        s0s1 = [| S0 > s0 < S1 ! S0S1 |]
        t0   : [ T0 s0 ]
        t0   = snd p0
        t1   : [ T1 s1 ]
        t1   = T0 s0 > t0 < T1 s1 ! T0T1 s0 s1 s0s1
    in  s1 , t1

  /W/ S0 T0 > (s0 <| f0) < /W/ S1 T1 ! Q =
    let S0S1 : Prf (S0 ⇔ S1)
        S0S1 = fst Q
        T1T0 : Prf (∏ S0 \s0 -> ∏ S1 \s1 -> (S0 > s0 ≅ S1 > s1) ⇒
                      (T1 s1 ⇔ T0 s0))
        T1T0 = snd Q
        s1   : [ S1 ]
        s1   = S0 > s0 < S1 ! S0S1
        s0s1 : Prf (S0 > s0 ≅ S1 > s1)
        s0s1 = [| S0 > s0 < S1 ! S0S1 |]
    in  s1 <| \t1 ->
        let t0   : [ T0 s0 ]
            t0   = T1 s1 > t1 < T0 s0 ! T1T0 s0 s1 s0s1
        in  /W/ S0 T0 > f0 t0 < /W/ S1 T1 ! Q

  /0/     > _ < /1/     ! ()
  /0/     > _ < /2/     ! ()
  /0/     > _ < /Π/ _ _ ! ()
  /0/     > _ < /Σ/ _ _ ! ()
  /0/     > _ < /W/ _ _ ! ()
  /1/     > _ < /0/     ! ()
  /1/     > _ < /2/     ! ()
  /1/     > _ < /Π/ _ _ ! ()
  /1/     > _ < /Σ/ _ _ ! ()
  /1/     > _ < /W/ _ _ ! ()
  /2/     > _ < /0/     ! ()
  /2/     > _ < /1/     ! ()
  /2/     > _ < /Π/ _ _ ! ()
  /2/     > _ < /Σ/ _ _ ! ()
  /2/     > _ < /W/ _ _ ! ()
  /Π/ _ _ > _ < /0/     ! ()
  /Π/ _ _ > _ < /1/     ! ()
  /Π/ _ _ > _ < /2/     ! ()
  /Π/ _ _ > _ < /Σ/ _ _ ! ()
  /Π/ _ _ > _ < /W/ _ _ ! ()
  /Σ/ _ _ > _ < /0/     ! ()
  /Σ/ _ _ > _ < /1/     ! ()
  /Σ/ _ _ > _ < /2/     ! ()
  /Σ/ _ _ > _ < /Π/ _ _ ! ()
  /Σ/ _ _ > _ < /W/ _ _ ! ()
  /W/ _ _ > _ < /0/     ! ()
  /W/ _ _ > _ < /1/     ! ()
  /W/ _ _ > _ < /2/     ! ()
  /W/ _ _ > _ < /Π/ _ _ ! ()
  /W/ _ _ > _ < /Σ/ _ _ ! ()

  [|_>_<_!_|] : (S : ∗)(s : [ S ])(T : ∗)(q : Prf (S ⇔ T)) ->
    Prf (S > s ≅ T > (S > s < T ! q))
  [| S > s < T ! q |] = {! !}

Resp : (S : ∗)(P : [ S ] -> ∗)
       {s0 s1 : [ S ]} -> Prf ((S > s0 ≅ S > s1) ⇒ (P s0 ⇔ P s1))
Resp = {! !}

[|_>_|] : (S : ∗)(s : [ S ]) -> Prf (S > s ≅ S > s)
[| S > s |] = {! !}

Sym : (S0 S1 : ∗) -> Prf ((S0 ⇔ S1) ⇒ (S1 ⇔ S0))
Sym = {! !}

sym : (S0 : ∗)(s0 : [ S0 ])(S1 : ∗)(s1 : [ S1 ]) ->
      Prf ((S0 > s0 ≅ S1 > s1) ⇒ (S1 > s1 ≅ S0 > s0))
sym = {! !}

elimNat∗ : (P : [ /Nat/ ] -> ∗) ->
           [( P zero ⟶ (/Π/ /Nat/ \k -> P k ⟶ P (suc k)) ⟶
              /Π/ /Nat/ \n -> P n )]
{-
elimNat∗ P pz ps (tt <| g) = P zero > pz < P (tt <| g) !
  Resp /Nat/ P (_ , \z0 -> z0 Ψ)
elimNat∗ P pz ps (ff <| g) =
  let n = g _
  in  P (suc n) > ps n (elimNat∗ P pz ps n) < P (ff <| g) !
         Resp /Nat/ P
           (_ , \u0 u1 u0u1 -> [| (/1/ ⟶ /Nat/) > g |] _ u1 _)
-}
elimNat∗ P pz ps n = rec P n
  \b -> case (\ b -> /Π/ ((Case b /0/ /1/) ⟶ /Nat/) \g ->
                        (/Π/ (Case b /0/ /1/) \t -> P (g t)) ⟶
                        P (b <| g)) b
    (\g _ -> P zero > pz < P (tt <| g) ! Resp /Nat/ P (_ , \z0 -> z0 Ψ))
    (\g h ->
       let n = g _
       in  P (suc n) > ps n (h _) < P (ff <| g) !
             Resp /Nat/ P
               (_ , \u0 u1 u0u1 -> [| (/1/ ⟶ /Nat/) > g |] _ u1 _))

plus : [ /Nat/ ⟶ /Nat/ ⟶ /Nat/ ]
plus x y = elimNat∗ (\_ -> /Nat/) y (\_ -> suc) x

irr : (P0 P1 : †) -> Prf ((|- P0 ⇔ |- P1) ⇒
      ∏ (|- P0) \p0 -> ∏ (|- P1) \p1 -> |- P0 > p0 ≅ |- P1 > p1)

irr ⊥  ⊥  _ _ _ = _

irr TT TT _ _ _ = _

irr (P0 ∧ Q0) (P1 ∧ Q1) PQ01 pq0 pq1 =
  let p01 : Prf (|- P0 > fst pq0 ≅ |- P1 > fst pq1)
      p01 = irr P0 P1 (fst PQ01) (fst pq0) (fst pq1)
  in  p01 , irr Q0 Q1 (snd PQ01 (fst pq0) (fst pq1) p01) (snd pq0) (snd pq1)

irr (∏ S0 P0) (∏ S1 P1) SP01 f0 f1 = \s0 s1 s0s1 ->
  irr (P0 s0) (P1 s1) (snd SP01 s1 s0 (sym S0 s0 S1 s1 s0s1)) (f0 s0) (f1 s1)

irr        ⊥  TT       () _ _
irr        ⊥  (_ ∧ _)  () _ _
irr        ⊥  (∏ _ _)  () _ _
irr       TT  ⊥        () _ _
irr       TT  (_ ∧ _)  () _ _
irr       TT  (∏ _ _)  () _ _
irr  (_ ∧ _)  TT       () _ _
irr  (_ ∧ _)  ⊥        () _ _
irr  (_ ∧ _)  (∏ _ _)  () _ _
irr  (∏ _ _)  TT       () _ _
irr  (∏ _ _)  ⊥        () _ _
irr  (∏ _ _)  (_ ∧ _)  () _ _

{---------------------------------------------------------------------------

	      The News from Nottingham (with subtitles)

			    Conor McBride

			   joint work with
	 Thorsten Altenkirch, Wouter Swierstra, Peter Hancock,
            Nicolas Oury, James Chapman and Peter Morris

---------------------------------------------------------------------------}

