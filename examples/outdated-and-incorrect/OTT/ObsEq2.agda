module ObsEq2 where

data Nat : Set where
  zero : Nat
  suc : Nat -> Nat

data Fin : Nat -> Set where
  fz : {n : Nat} -> Fin (suc n)
  fs : {n : Nat} -> Fin n -> Fin (suc n)

infixr 40 _::_ _,_

data List (X : Set) : Set where
  ε : List X
  _::_ : X -> List X -> List X

record One : Set where

Π : (S : Set)(T : S -> Set) -> Set
Π S T = (x : S) -> T x

data Σ (S : Set)(T : S -> Set) : Set where
  _,_ : (s : S) -> T s -> Σ S T

split : {S : Set}{T : S -> Set}{P : Σ S T -> Set}
        (p : (s : S)(t : T s) -> P (s , t)) ->
        (x : Σ S T) -> P x
split p (s , t) = p s t

fst : {S : Set}{T : S -> Set}(x : Σ S T) -> S
fst = split \s t -> s

snd : {S : Set}{T : S -> Set}(x : Σ S T) -> T (fst x)
snd = split \s t -> t

mutual

  data ∗ : Set where
    /Π/ : (S : ∗)(T : [ S ] -> ∗) -> ∗
    /Σ/ : (S : ∗)(T : [ S ] -> ∗) -> ∗
    /Fin/ : Nat -> ∗
    /D/ : (I : ∗)(A : [ I ] -> ∗)(R : (i : [ I ]) -> [ A i ] -> List [ I ])
        -> [ I ] -> ∗

  [_] : ∗ -> Set
  [ /Π/ S T ]    = Π [ S ] \s -> [ T s ]
  [ /Σ/ S T ]    = Σ [ S ] \s -> [ T s ]
  [ /Fin/ n ]    = Fin n
  [ /D/ I A R i ]  = Σ [ A i ] \a -> [ Kids I (/D/ I A R) (R i a) ]

  Kids : (I : ∗)(P : [ I ] -> ∗) -> List [ I ] -> ∗
  Kids I P ε = /Fin/ (suc zero)
  Kids I P (i :: is) = /Σ/ (P i) \_ -> Kids I P is

/0/ : ∗
/0/ = /Fin/ zero

/1/ : ∗
/1/ = /Fin/ (suc zero)

/2/ : ∗
/2/ = /Fin/ (suc (suc zero))

Branches : {n : Nat}(P : Fin n -> Set) -> Set
Branches {zero} P = One
Branches {suc n} P = Σ (P fz) \_ -> Branches {n} \x -> P (fs x)

case : {n : Nat}{P : Fin n -> Set} -> Branches P -> (x : Fin n) -> P x
case pps  fz     = fst pps
case pps (fs x)  = case (snd pps) x


infixr 40 _⟶_

infixr 60 _×_

_⟶_ : ∗ -> ∗ -> ∗
S ⟶ T = /Π/ S \_ -> T

_×_ : ∗ -> ∗ -> ∗
S × T = /Σ/ S \_ -> T

NatR : [ /1/ ] -> [ /2/ ] -> List [ /1/ ]
NatR _ fz       = ε
NatR _ (fs fz)  = fz :: ε
NatR _ (fs (fs ()))

/Nat/ : ∗
/Nat/ = /D/ /1/ (\_ -> /2/) NatR fz

/zero/ : [ /Nat/ ]
/zero/ = fz , fz

/suc/ : [ /Nat/ ⟶ /Nat/ ]
/suc/ n = fs fz , n , fz

Hyps : (I : ∗)(K : [ I ] -> ∗)
       (P : (i : [ I ]) -> [ K i ] -> ∗)
       (is : List [ I ]) -> [ Kids I K is ] -> ∗
Hyps I K P  ε          _       = /1/
Hyps I K P  (i :: is) (k , ks) = /Σ/ (P i k) \_ -> Hyps I K P is ks

recs : (I : ∗)(K : [ I ] -> ∗)
       (P : (i : [ I ]) -> [ K i ] -> ∗)
       (e : (i : [ I ])(k : [ K i ]) -> [ P i k ])
       (is : List [ I ])(ks : [ Kids I K is ]) -> [ Hyps I K P is ks ]
recs I K P e  ε          _ = fz
recs I K P e  (i :: is) (k , ks) = ( e i k , recs I K P e is ks )

elim : (I : ∗)(A : [ I ] -> ∗)(R : (i : [ I ]) -> [ A i ] -> List [ I ])
       (P : (i : [ I ]) -> [ /D/ I A R i ] -> ∗) ->
       [( (/Π/ I \i -> /Π/ (A i) \a ->
          /Π/ (Kids I (/D/ I A R) (R i a)) \ks ->
          Hyps I (/D/ I A R) P (R i a) ks ⟶ P i (a , ks)) ⟶
         /Π/ I \i -> /Π/ (/D/ I A R i) \x -> P i x )]
elim I A R P p i (a , ks) =
  p i a ks (recs I (/D/ I A R) P (elim I A R P p) (R i a) ks)

natElim : (P : [ /Nat/ ] -> ∗) ->
          [( P /zero/ ⟶
             (/Π/ /Nat/ \n -> P n ⟶ P (/suc/ n)) ⟶
             /Π/ /Nat/ P )]
natElim P pz ps = elim /1/ (\_ -> /2/) NatR (case (P , _))
  (case ( case (case ((\_ -> pz ) , _ )
  , (split \n -> case (split (\h _ -> ps n h)   , _ ))   , _ )  , _ ))
  fz


plus : [ /Nat/ ⟶ /Nat/ ⟶ /Nat/ ]
plus x y = natElim (\_ -> /Nat/) y (\_ -> /suc/) x

{-
elim /1/ (\_ -> /2/) NatR (\_ _ -> /Nat/)
   (\_ -> case
    ((\_ _ -> y )
    , split (\_ _ -> split (\n _ -> /suc/ n )  )  , _ ) )
   fz x
-}

mutual
  _⇔_ : ∗ -> ∗ -> ∗
  /Π/ S0 T0 ⇔ /Π/ S1 T1 =
    (S1 ⇔ S0) ×
    /Π/ S1 \s1 -> /Π/ S0 \s0 -> (S1 > s1 ≅ S0 > s0) ⟶ (T0 s0 ⇔ T1 s1)
  /Σ/ S0 T0 ⇔ /Σ/ S1 T1 =
    (S0 ⇔ S1) ×
    /Π/ S0 \s0 -> /Π/ S1 \s1 -> (S0 > s0 ≅ S1 > s1) ⟶ (T0 s0 ⇔ T1 s1)
  /Fin/ _ ⇔ /Π/ _ _ = /0/
  /Fin/ _ ⇔ /Σ/ _ _ = /0/
  /Fin/ _ ⇔ /D/ _ _ _ _ = /0/
  /Π/ _ _ ⇔ /Fin/ _ = /0/
  /Σ/ _ _ ⇔ /Fin/ _ = /0/
  /D/ _ _ _ _ ⇔ /Fin/ _ = /0/
  /Fin/ zero ⇔ /Fin/ zero = /1/
  /Fin/ (suc m) ⇔ /Fin/ (suc n) = /Fin/ m ⇔ /Fin/ n
  /D/ I0 A0 R0 i0 ⇔ /D/ I1 A1 R1 i1 =
    (I0 ⇔ I1) ×
    (/Π/ I0 \i0 -> /Π/ I1 \i1 -> (I0 > i0 ≅ I1 > i1) ⟶ (A0 i0 ⇔ A1 i1)) ×
    (/Π/ I0 \i0 -> /Π/ I1 \i1 -> (I0 > i0 ≅ I1 > i1) ⟶
     /Π/ (A0 i0) \a0 -> /Π/ (A1 i1) \a1 -> (A0 i0 > a0 ≅ A1 i1 > a1) ⟶
     Eqs I0 (R0 i0 a0) I1 (R1 i1 a1)) ×
    (I0 > i0 ≅ I1 > i1)
  _ ⇔ _ = /0/

  Eqs : (I0 : ∗) -> List [ I0 ] -> (I1 : ∗) -> List [ I1 ] -> ∗
  Eqs _ ε _ ε = /1/
  Eqs I0 (i0 :: is0) I1 (i1 :: is1) = (I0 > i0 ≅ I1 > i1) × Eqs I0 is0 I1 is1
  Eqs _ _ _ _ = /0/

  _>_≅_>_ : (S : ∗) -> [ S ] -> (T : ∗) -> [ T ] -> ∗
  /Π/ S0 T0 > f0 ≅ /Π/ S1 T1 > f1 =
    /Π/ S0 \s0 -> /Π/ S1 \s1 -> (S0 > s0 ≅ S1 > s1) ⟶
       (T0 s0 > f0 s0 ≅ T1 s1 > f1 s1)
  /Σ/ S0 T0 > p0 ≅ /Σ/ S1 T1 > p1 =
    let s0 : [ S0 ] ; s0 = fst p0
        s1 : [ S1 ] ; s1 = fst p1
    in  (S0 > s0 ≅ S1 > s1) × (T0 s0 > snd p0 ≅ T1 s1 > snd p1)
  /Fin/ (suc n0) > fz    ≅ /Fin/ (suc n1) > fz    = /1/
  /Fin/ (suc n0) > fs x0 ≅ /Fin/ (suc n1) > fs x1 =
    /Fin/ n0 > x0 ≅ /Fin/ n1 > x1
  /D/ I0 A0 R0 i0 > (a0 , ks0) ≅ /D/ I1 A1 R1 i1 > (a1 , ks1) =
    (A0 i0 > a0 ≅ A1 i1 > a1) ×
    (Kids I0 (/D/ I0 A0 R0) (R0 i0 a0) > ks0 ≅
     Kids I1 (/D/ I1 A1 R1) (R1 i1 a1) > ks1)

  _ > _ ≅ _ > _ = /0/

Resp : (S : ∗)(P : [ S ] -> ∗)
       {s0 s1 : [ S ]} -> [ (S > s0 ≅ S > s1) ⟶ (P s0 ⇔ P s1) ]
Resp = {! !}

[_>_] : (S : ∗)(s : [ S ]) -> [ S > s ≅ S > s ]
[_>_] = {! !}

KidsResp : (I0 : ∗)(I1 : ∗) -> [ I0 ⇔ I1 ] ->
           (P0 : [ I0 ] -> ∗)(P1 : [ I1 ] -> ∗) ->
           [( /Π/ I0 \i0 -> /Π/ I1 \i1 -> (I0 > i0 ≅ I1 > i1) ⟶
              (P0 i0 ⇔ P1 i1) )] ->
           (is0 : List [ I0 ])(is1 : List [ I1 ]) ->
           [ Eqs I0 is0 I1 is1 ] ->
           [ Kids I0 P0 is0 ⇔ Kids I1 P1 is1 ]
KidsResp = {! !}

mutual

  _>_<_!_ : (S : ∗) -> [ S ] -> (T : ∗) -> [ S ⇔ T ] -> [ T ]
  /Π/ S0 T0 > f0 < /Π/ S1 T1 ! Q =
    let S1S0 : [ S1 ⇔ S0 ]
        S1S0 = fst Q
        T0T1 : [( /Π/ S1 \s1 -> /Π/ S0 \s0 -> (S1 > s1 ≅ S0 > s0) ⟶
                  (T0 s0 ⇔ T1 s1) )]
        T0T1 = snd Q
    in  \s1 ->
        let s0   : [ S0 ]
            s0   = S1 > s1 < S0 ! S1S0
            s1s0 : [( S1 > s1 ≅ S0 > s0 )]
            s1s0 = [| S1 > s1 < S0 ! S1S0 |]
        in  T0 s0 > f0 s0 < T1 s1 ! T0T1 s1 s0 s1s0

  /Σ/ S0 T0 > p0 < /Σ/ S1 T1 ! Q =
    let S0S1 : [ S0 ⇔ S1 ]
        S0S1 = fst Q
        T0T1 : [( /Π/ S0 \s0 -> /Π/ S1 \s1 -> (S0 > s0 ≅ S1 > s1) ⟶
                      (T0 s0 ⇔ T1 s1) )]
        T0T1 = snd Q
        s0   : [ S0 ]
        s0   = fst p0
        s1   : [ S1 ]
        s1   = S0 > s0 < S1 ! S0S1
        s0s1 : [ S0 > s0 ≅ S1 > s1 ]
        s0s1 = [| S0 > s0 < S1 ! S0S1 |]
        t0   : [ T0 s0 ]
        t0   = snd p0
        t1   : [ T1 s1 ]
        t1   = T0 s0 > t0 < T1 s1 ! T0T1 s0 s1 s0s1
    in  s1 , t1

  /Fin/ (suc n0) > fz   < /Fin/ (suc n1) ! Q = fz
  /Fin/ (suc n0) > fs x < /Fin/ (suc n1) ! Q = fs (/Fin/ n0 > x < /Fin/ n1 ! Q)

  /D/ I0 A0 R0 i0 > (a0 , ks0) < /D/ I1 A1 R1 i1 ! Q =
    let I01 : [ I0 ⇔ I1 ] ; I01 = fst Q
        A01 : [( /Π/ I0 \i0 -> /Π/ I1 \i1 ->
                 (I0 > i0 ≅ I1 > i1) ⟶ (A0 i0 ⇔ A1 i1) )]
        A01 = fst (snd Q)
        R01 : [( /Π/ I0 \i0 -> /Π/ I1 \i1 -> (I0 > i0 ≅ I1 > i1) ⟶
                 /Π/ (A0 i0) \a0 -> /Π/ (A1 i1) \a1 ->
                 (A0 i0 > a0 ≅ A1 i1 > a1) ⟶
                 Eqs I0 (R0 i0 a0) I1 (R1 i1 a1) )]
        R01 = fst (snd (snd Q))
        i01 : [ I0 > i0 ≅ I1 > i1 ] ; i01 = snd (snd (snd Q))
    in  (/Σ/ (A0 i0) \a0 -> Kids I0 (/D/ I0 A0 R0) (R0 i0 a0)) > (a0 , ks0) <
        (/Σ/ (A1 i1) \a1 -> Kids I1 (/D/ I1 A1 R1) (R1 i1 a1)) !
        A01 i0 i1 i01 ,
        \x0 x1 x01 ->
          KidsResp I0 I1 I01
          (/D/ I0 A0 R0) (/D/ I1 A1 R1) (\j0 j1 j01 -> I01 , A01 , R01 , j01 )
          (R0 i0 x0) (R1 i1 x1) (R01 i0 i1 i01 x0 x1 x01)

  /Π/ _ _ > _ < /Σ/ _ _ ! ()
  /Π/ _ _ > _ < /Fin/ _ ! ()
  /Π/ _ _ > _ < /D/ _ _ _ _ ! ()

  /Σ/ _ _ > _ < /Π/ _ _ ! ()
  /Σ/ _ _ > _ < /Fin/ _ ! ()
  /Σ/ _ _ > _ < /D/ _ _ _ _ ! ()

  /D/ _ _ _ _ > _ < /Π/ _ _ ! ()
  /D/ _ _ _ _ > _ < /Σ/ _ _ ! ()
  /D/ _ _ _ _ > _ < /Fin/ _ ! ()

  /Fin/ _ > _ < /Π/ _ _ ! ()
  /Fin/ _ > _ < /Σ/ _ _ ! ()
  /Fin/ zero > () < /Fin/ zero ! _
  /Fin/ zero > _ < /Fin/ (suc n) ! ()
  /Fin/ (suc n) > _ < /Fin/ zero ! ()
  /Fin/ _ > _ < /D/ _ _ _ _ ! ()

  [|_>_<_!_|] : (S : ∗)(s : [ S ])(T : ∗)(q : [ S ⇔ T ]) ->
    [ S > s ≅ T > (S > s < T ! q) ]
  [| S > s < T ! q |] = {! !}

ext : (S : ∗)(T : [ S ] -> ∗)(f g : [ /Π/ S T ]) ->
      [( /Π/ S \x -> T x > f x ≅ T x > g x )] ->
      [ /Π/ S T > f ≅ /Π/ S T > g ]
ext S T f g h s0 s1 s01 =
  (T s0 > f s0 ≅ T s0 > g s0) > h s0 < (T s0 > f s0 ≅ T s1 > g s1) !
  Resp S (\s1 -> T s0 > f s0 ≅ T s1 > g s1) s01

plusZeroLemma : [ (/Nat/ ⟶ /Nat/) > (\x -> plus x /zero/) ≅
                  (/Nat/ ⟶ /Nat/) > (\x -> plus /zero/ x) ]
plusZeroLemma = ext /Nat/ (\_ -> /Nat/)
   (\x -> plus x /zero/) (\x -> plus /zero/ x) (natElim (\x ->
     /Nat/ > plus x /zero/ ≅ /Nat/ > plus /zero/ x) (fz , fz)
    (\n h -> [ (/Nat/ ⟶ /Nat/) > /suc/ ] (plus n /zero/) n h  ))
