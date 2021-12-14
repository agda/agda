{-# OPTIONS --no-positivity-check
            --no-termination-check
  #-}

-- A universe setoids
module Setoid where

import Chain

record True : Set where
data False : Set where

Rel : Set -> Set1
Rel A = A -> A -> Set

Pred : Set -> Set1
Pred A = A -> Set

Resp : {A : Set} -> Rel A -> {B : Set} -> Rel B -> Pred (A -> B)
Resp _R_ _S_ f = forall x y -> x R y -> f x S f y

_∋_ : (A : Set) → A → A
A ∋ x = x

mutual

  infixr 10 _,_
  infix  40 _=El=_ _=S=_ _=Fam=_
  infix  60 _!_

  data Setoid : Set where
    nat : Setoid
    Π   : (A : Setoid)(F : Fam A) -> Setoid
    Σ   : (A : Setoid)(F : Fam A) -> Setoid

  data Fam (A : Setoid) : Set where
    fam : (F : El A -> Setoid) ->
          Resp _=El=_ _=S=_ F -> Fam A

  data El : Setoid -> Set where
    zero : El nat
    suc  : El nat -> El nat
    ƛ    : {A : Setoid}{F : Fam A}
           (f : (x : El A) -> El (F ! x)) ->
           ((x y : El A) -> x =El= y -> f x =El= f y) -> El (Π A F)
    _,_  : {A : Setoid}{F : Fam A}(x : El A) -> El (F ! x) -> El (Σ A F)

  data _=S=_ : (A B : Setoid) -> Set where
    eqNat : nat =S= nat
    eqΠ   : {A₁ A₂ : Setoid}{F₁ : Fam A₁}{F₂ : Fam A₂} ->
             A₂ =S= A₁ -> F₁ =Fam= F₂ -> Π A₁ F₁ =S= Π A₂ F₂
    eqΣ   : {A₁ A₂ : Setoid}{F₁ : Fam A₁}{F₂ : Fam A₂} ->
            A₁ =S= A₂ -> F₁ =Fam= F₂ -> Σ A₁ F₁ =S= Σ A₂ F₂

  data _=El=_ : {A B : Setoid} -> El A -> El B -> Set where
    eqInNat : {n : El nat} -> n =El= n
    eqInΠ   : {A₁ A₂ : Setoid}{F₁ : Fam A₁}{F₂ : Fam A₂}
              {f₁ : (x : El A₁) -> El (F₁ ! x)}
              {pf₁ : (x y : El A₁) -> x =El= y -> f₁ x =El= f₁ y}
              {f₂ : (x : El A₂) -> El (F₂ ! x)} ->
              {pf₂ : (x y : El A₂) -> x =El= y -> f₂ x =El= f₂ y} ->
              A₂ =S= A₁ ->
              ((x : El A₁)(y : El A₂) -> x =El= y -> f₁ x =El= f₂ y) ->
              (El (Π A₁ F₁) ∋ ƛ f₁ pf₁) =El= (El (Π A₂ F₂) ∋ ƛ f₂ pf₂)
    eqInΣ   : {A₁ A₂ : Setoid}{F₁ : Fam A₁}{F₂ : Fam A₂}
              {x₁ : El A₁}{y₁ : El (F₁ ! x₁)}
              {x₂ : El A₂}{y₂ : El (F₂ ! x₂)} ->
              F₁ =Fam= F₂ -> x₁ =El= x₂ -> y₁ =El= y₂ -> (El (Σ A₁ F₁) ∋ (x₁ , y₁ )) =El= (El (Σ A₂ F₂) ∋ (x₂ , y₂))

  data _=Fam=_ {A B : Setoid}(F : Fam A)(G : Fam B) : Set where
    eqFam : B =S= A -> (forall x y -> x =El= y -> F ! x =S= G ! y) -> F =Fam= G

  _!_ : {A : Setoid} -> Fam A -> El A -> Setoid
  fam F _ ! x = F x

-- Inversions
famEqDom : {A B : Setoid}{F : Fam A}{G : Fam B} -> F =Fam= G -> B =S= A
famEqDom (eqFam p _) = p

famEqCodom : {A B : Setoid}{F : Fam A}{G : Fam B} -> F =Fam= G ->
        (x : El A)(y : El B) -> x =El= y -> F ! x =S= G ! y
famEqCodom (eqFam _ p) = p

eqΠ-inv₁ : {A₁ A₂ : Setoid}{F₁ : Fam A₁}{F₂ : Fam A₂} ->
           Π A₁ F₁ =S= Π A₂ F₂ -> A₂ =S= A₁
eqΠ-inv₁ (eqΠ p _) = p

eqΠ-inv₂ : {A₁ A₂ : Setoid}{F₁ : Fam A₁}{F₂ : Fam A₂} ->
           Π A₁ F₁ =S= Π A₂ F₂ -> F₁ =Fam= F₂
eqΠ-inv₂ (eqΠ _ p) = p

eqΣ-inv₁ : {A₁ A₂ : Setoid}{F₁ : Fam A₁}{F₂ : Fam A₂} ->
           Σ A₁ F₁ =S= Σ A₂ F₂ -> A₁ =S= A₂
eqΣ-inv₁ (eqΣ p _) = p

eqΣ-inv₂ : {A₁ A₂ : Setoid}{F₁ : Fam A₁}{F₂ : Fam A₂} ->
           Σ A₁ F₁ =S= Σ A₂ F₂ -> F₁ =Fam= F₂
eqΣ-inv₂ (eqΣ _ p) = p

-- Equivalence proofs and casts
mutual

  -- _=Fam=_ is an equivalence
  =Fam=-refl : {A : Setoid}{F : Fam A} -> F =Fam= F
  =Fam=-refl {F = fam _ p} = eqFam =S=-refl p

  =Fam=-sym : {A B : Setoid}{F : Fam A}{G : Fam B} -> F =Fam= G -> G =Fam= F
  =Fam=-sym (eqFam B=A F=G) = eqFam (=S=-sym B=A) \x y x=y -> =S=-sym (F=G _ _ (=El=-sym x=y))

  =Fam=-trans : {A B C : Setoid}{F : Fam A}{G : Fam B}{H : Fam C} ->
                F =Fam= G -> G =Fam= H -> F =Fam= H
  =Fam=-trans (eqFam B=A F=G) (eqFam C=B G=H) =
    eqFam (=S=-trans C=B B=A) \x y x=y ->
           =S=-trans (F=G x (B=A << x) (cast-id _))
                     (G=H _ y (=El=-trans (=El=-sym (cast-id _)) x=y))

  -- _=S=_ is an equivalence
  =S=-refl : {A : Setoid} -> A =S= A
  =S=-refl {nat}   = eqNat
  =S=-refl {Π A F} = eqΠ =S=-refl =Fam=-refl
  =S=-refl {Σ A F} = eqΣ =S=-refl =Fam=-refl

  =S=-sym : {A B : Setoid} -> A =S= B -> B =S= A
  =S=-sym eqNat = eqNat
  =S=-sym (eqΠ pA pF) = eqΠ (=S=-sym pA) (=Fam=-sym pF)
  =S=-sym (eqΣ pA pF) = eqΣ (=S=-sym pA) (=Fam=-sym pF)

  =S=-trans : {A B C : Setoid} -> A =S= B -> B =S= C -> A =S= C
  =S=-trans eqNat eqNat = eqNat
  =S=-trans (eqΠ B=A F=G) (eqΠ C=B G=H) = eqΠ (=S=-trans C=B B=A) (=Fam=-trans F=G G=H)
  =S=-trans (eqΣ A=B F=G) (eqΣ B=C G=H) = eqΣ (=S=-trans A=B B=C) (=Fam=-trans F=G G=H)

  -- _=El=_ is an equivalence
  =El=-refl : {A : Setoid}{x : El A} -> x =El= x
  =El=-refl {nat}   = eqInNat
  =El=-refl {Π A F}{ƛ f pf} = eqInΠ =S=-refl pf
  =El=-refl {Σ A F}{x , y}  = eqInΣ =Fam=-refl =El=-refl =El=-refl

  =El=-sym : {A B : Setoid}{x : El A}{y : El B} -> x =El= y -> y =El= x
  =El=-sym eqInNat = eqInNat
  =El=-sym (eqInΠ B=A p) = eqInΠ (=S=-sym B=A) \x y x=y -> =El=-sym (p y x (=El=-sym x=y))
  =El=-sym (eqInΣ pF px py) = eqInΣ (=Fam=-sym pF) (=El=-sym px) (=El=-sym py)

  =El=-trans : {A B C : Setoid}{x : El A}{y : El B}{z : El C} ->
             x =El= y -> y =El= z -> x =El= z
  =El=-trans eqInNat eqInNat = eqInNat
  =El=-trans (eqInΠ B=A f=g) (eqInΠ C=B g=h) =
    eqInΠ (=S=-trans C=B B=A) \x y x=y ->
      =El=-trans (f=g x (B=A << x) (cast-id _))
               (g=h _ y (=El=-trans (=El=-sym (cast-id _)) x=y))
  =El=-trans (eqInΣ F₁=F₂ x₁=x₂ y₁=y₂) (eqInΣ F₂=F₃ x₂=x₃ y₂=y₃) =
    eqInΣ (=Fam=-trans F₁=F₂ F₂=F₃) (=El=-trans x₁=x₂ x₂=x₃) (=El=-trans y₁=y₂ y₂=y₃)

  -- Casting. Important: don't look at the proof!
  infix 50 _<<_ _>>_

  _<<_ : {A B : Setoid} -> A =S= B -> El B -> El A
  _<<_ {nat}{Π _ _}   () _
  _<<_ {nat}{Σ _ _}   () _
  _<<_ {Π _ _}{nat}   () _
  _<<_ {Π _ _}{Σ _ _} () _
  _<<_ {Σ _ _}{nat}   () _
  _<<_ {Σ _ _}{Π _ _} () _
  _<<_ {nat}{nat} p x = x
  _<<_ {Π A₁ F₁}{Π A₂ F₂} p (ƛ f pf) = ƛ g pg
    where
      g : (x : El A₁) -> El (F₁ ! x)
      g x = let A₂=A₁ = eqΠ-inv₁ p
                F₁=F₂ = famEqCodom (eqΠ-inv₂ p) x _ (cast-id _)
            in  F₁=F₂ << f (A₂=A₁ << x)

      pg : (x y : El A₁) -> x =El= y -> g x =El= g y
      pg x y x=y = cast-irr _ _ (pf _ _ (cast-irr _ _ x=y))

  _<<_ {Σ A₁ F₁}{Σ A₂ F₂} p (x , y) = eqΣ-inv₁ p << x , F₁=F₂ << y
    where
      F₁=F₂ : F₁ ! (eqΣ-inv₁ p << x) =S= F₂ ! x
      F₁=F₂ = famEqCodom (eqΣ-inv₂ p) _ _ (=El=-sym (cast-id _))

  _>>_ : {A B : Setoid} -> Fam A -> A =S= B -> Fam B
  fam F pF >> A=B = fam G pG
    where
      G : El _ -> Setoid
      G y = F (A=B << y)

      pG : forall x y -> x =El= y -> G x =S= G y
      pG x y x=y = pF _ _ (cast-irr _ _ x=y)

  cast-id : {A B : Setoid}{x : El A}(p : B =S= A) -> x =El= p << x
  cast-id eqNat = eqInNat
  cast-id {x = x , y } (eqΣ A=B F=G) = eqInΣ (=Fam=-sym F=G) (cast-id _) (cast-id _)
  cast-id {x = ƛ f pf} (eqΠ B=A F=G) =
    eqInΠ (=S=-sym B=A) \x y x=y ->
      proof f x
          ≡ f (_ << y)      by pf _ _ (=El=-trans x=y (cast-id _))
          ≡ _ << f (_ << y) by cast-id _
      qed
    where
      open Chain El _=El=_ (\x -> =El=-refl) (\x y z -> =El=-trans)

  cast-irr : {A₁ A₂ B₁ B₂ : Setoid}{x : El A₁}{y : El A₂}
             (p₁ : B₁ =S= A₁)(p₂ : B₂ =S= A₂) -> x =El= y -> p₁ << x =El= p₂ << y
  cast-irr {x = x}{y = y} p q x=y =
    proof p << x
        ≡ x by =El=-sym (cast-id _)
        ≡ y by x=y
        ≡ q << y by cast-id _
    qed
    where
      open Chain El _=El=_ (\x -> =El=-refl) (\x y z -> =El=-trans)

-- Let's do some overloading

data EqFam : Set -> Set where
  el     : EqFam Setoid
  setoid : EqFam True
  fam    : EqFam Setoid

[_] : {I : Set} -> EqFam I -> I -> Set
[ el ]     A = El A
[ setoid ] _ = Setoid
[ fam ]    A = Fam A

infix 5 _==_

_==_ : {I : Set}{eqf : EqFam I}{i j : I} -> [ eqf ] i -> [ eqf ] j -> Set
_==_ {eqf = el    } x y = x =El= y
_==_ {eqf = setoid} A B = A =S= B
_==_ {eqf = fam   } F G = F =Fam= G

refl : {I : Set}{eqf : EqFam I}{i : I}{x : [ eqf ] i} -> x == x
refl {eqf = el}     = =El=-refl
refl {eqf = setoid} = =S=-refl
refl {eqf = fam}    = =Fam=-refl

sym : {I : Set}{eqf : EqFam I}{i j : I}{x : [ eqf ] i}{y : [ eqf ] j} -> x == y -> y == x
sym {eqf = el}     = =El=-sym
sym {eqf = setoid} = =S=-sym
sym {eqf = fam}    = =Fam=-sym

trans : {I : Set}{eqf : EqFam I}{i j k : I}{x : [ eqf ] i}{y : [ eqf ] j}{z : [ eqf ] k} ->
        x == y -> y == z -> x == z
trans {eqf = el}     = =El=-trans
trans {eqf = setoid} = =S=-trans
trans {eqf = fam}    = =Fam=-trans

open module EqChain {I : Set}{eqf : EqFam I} =
  Chain ([ eqf ]) _==_ (\x -> refl) (\x y z -> trans)

homo : {A B : Setoid}{x : El A}{y : El B} -> x == y -> A == B
homo eqInNat = eqNat
homo (eqInΠ B=A p) = eqΠ B=A (eqFam B=A \x y x=y -> homo (p x y x=y))
homo (eqInΣ F=G p q) = eqΣ (homo p) F=G

cast-id' : {A B C : Setoid}{x : El A}{y : El B}(p : C == B) -> x == y -> x == p << y
cast-id' C=B x=y = trans x=y (cast-id _)

-- Some helper stuff
K : {A : Setoid} -> Setoid -> Fam A
K B = fam (\_ -> B) (\_ _ _ -> refl)

infixr 20 _==>_
infixl 70 _·_ _∘_ _○_
infixl 90 _#_

!-cong : {A B : Setoid}(F : Fam A)(G : Fam B){x : El A}{y : El B} ->
         F == G -> x == y -> F ! x == G ! y
!-cong F G (eqFam B=A F=G) x=y = F=G _ _ x=y

!-cong-R : {A : Setoid}(F : Fam A){x y : El A} ->
           x == y -> F ! x == F ! y
!-cong-R F x=y = !-cong F F refl x=y

_==>_ : Setoid -> Setoid -> Setoid
A ==> B = Π A (K B)

_#_ : {A : Setoid}{F : Fam A} -> El (Π A F) -> (x : El A) -> El (F ! x)
ƛ f _ # x = f x

#-cong : {A B : Setoid}{F : Fam A}{G : Fam B}
         (f : El (Π A F))(g : El (Π B G)){x : El A}{y : El B} ->
         f == g -> x == y -> f # x == g # y
#-cong ._ ._ (eqInΠ _ f=g) x=y = f=g _ _ x=y

#-cong-R : {A : Setoid}{F : Fam A}(f : El (Π A F)){x y : El A} ->
           x == y -> f # x == f # y
#-cong-R f p = #-cong f f refl p

id : {A : Setoid} -> El (A ==> A)
id = ƛ (\x -> x) (\_ _ p -> p)

-- Family composition
_○_ : {A B : Setoid} -> Fam A -> El (B ==> A) -> Fam B
F ○ f = fam (\x -> F ! (f # x)) (\x y x=y -> !-cong-R F (#-cong-R f x=y))

lem-○-id : {A : Setoid}{F : Fam A} -> F ○ id == F
lem-○-id {F = F} = eqFam refl \x y x=y -> !-cong-R F x=y

_∘_ : {A B : Setoid}{F : Fam B} -> El (Π B F) -> (g : El (A ==> B)) -> El (Π A (F ○ g))
f ∘ g = ƛ (\x -> f # (g # x)) \x y x=y -> #-cong-R f (#-cong-R g x=y)

lem-∘-id : {A : Setoid}{F : Fam A}(f : El (Π A F)) -> f ∘ id == f
lem-∘-id (ƛ f pf) = eqInΠ refl pf

lem-id-∘ : {A B : Setoid}(f : El (A ==> B)) -> id ∘ f == f
lem-id-∘ (ƛ f pf) = eqInΠ refl pf

-- Simply type composition (not quite a special case of ∘ because of proof relevance)
_·_ : {A B C : Setoid} -> El (B ==> C) -> El (A ==> B) -> El (A ==> C)
f · g = eqΠ refl (eqFam refl \_ _ _ -> refl) << f ∘ g

fst : {A : Setoid}{F : Fam A} -> El (Σ A F) -> El A
fst (x , y) = x

snd : {A : Setoid}{F : Fam A}(p : El (Σ A F)) -> El (F ! fst p)
snd (x , y) = y

fst-eq : {A B : Setoid}{F : Fam A}{G : Fam B}
         {x : El (Σ A F)}{y : El (Σ B G)} -> x == y -> fst x == fst y
fst-eq (eqInΣ _ x₁=x₂ _) = x₁=x₂

snd-eq : {A B : Setoid}{F : Fam A}{G : Fam B}
        {x : El (Σ A F)}{y : El (Σ B G)} -> x == y -> snd x == snd y
snd-eq (eqInΣ _ _ y₁=y₂) = y₁=y₂

η : {A : Setoid}{F : Fam A}(f : El (Π A F)){pf : (x y : El A) -> x == y -> f # x == f # y} ->
    f == ƛ {F = F} (_#_ f) pf
η (ƛ f pf) = eqInΠ refl pf
