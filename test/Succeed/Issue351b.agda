module _ where

postulate
  T U V : Set
  F G : Set → Set
  Sea : {A : Set} → (A → A → Set) → Set
  Seas : {I : Set} (As : I → Set) → ({i j : I} → As i → As j → Set) → Set
  _eq_ _to_ : T → T → Set

record K : Set₁ where
  field
    A : Set
    B : A → A → Set
    C : Sea B

record IK (I : Set) : Set₁ where
  field
    As : I → Set
    Bs : {i j : I} → As i → As j → Set
    Cs : Seas As Bs

open K
open IK

record L (f t : K) : Set where
  field
    D : A f → A t
    E : ∀ {x y} → (B f x y) → B t (D x) (D y)

record IL (f : K) (t : IK (A f)): Set where
  field
    Ds : (x : A f) → As t x
    Es : ∀ {x y} → (B f x y) → Bs t (Ds x) (Ds y)

-- make Cs or E irrelevant and the last line turns yellow
postulate blah : ∀ {a b c : K} → L a b → L b c → L a c

foop : ∀ {a b c d : K} → L a b → L b c → L c d → L a d
foop f g h = blah f (blah g h)

postulate Equiv : Sea _eq_

Cat : K
Cat = record
  { A = T
  ; B = _eq_
  ; C = Equiv
  }

record T2 : Set where
  constructor _,_
  field fst snd : T

open T2

record _eq2_ (a b : T2) : Set where
  constructor _∧_
  field
    feq : (fst a) eq (fst b)
    seq : (snd a) eq (snd b)

postulate Equiv2 : Sea _eq2_

Cat2 : K
Cat2 = record { A = T2; B = _eq2_; C = Equiv2 }

postulate
  Hm : T2 → Set
  _heq_ : {t t' : T2} → Hm t → Hm t' → Set
  HEquiv : Seas Hm _heq_

Hom : IK T2
Hom = record
  { As = Hm
  ; Bs = _heq_
  ; Cs = HEquiv
  }

_×_ : ∀ {U} → L U Cat → L U Cat → L U Cat2
X × Y = record { D = λ x → L.D X x , L.D Y x
               ; E = λ x' → L.E X x' ∧ L.E Y x' }

postulate
  _∘_ : ∀ {a b c} → Hm (b , c) → Hm (a , b) → Hm (a , c)
  ∘cong : ∀ {a b c} {f f' : Hm (b , c)} {g g' : Hm (a , b)} → f heq f' → g heq g' → (f ∘ g) heq (f' ∘ g')
  _∘H_ : ∀ {a b c} → Hm (b , c) → Hm (a , b) → Hm (a , c)

module Fool (Base : K) where
  Dust = L Base Cat

  promote : L Base Cat2 → IK (A Base)
  promote f = record
    { As = λ x → Hm (L.D f x)
    ; Bs = λ x y → x heq y
    ; Cs = my-Cs
    }
    where
    postulate my-Cs : Seas (λ x → Hm (L.D f x)) (λ {i} {j} x y → x heq y)

  Dance : Dust → Dust → Set
  Dance f t = IL Base (promote (f × t))

  _⊚_ : ∀ {as bs cs} → Dance bs cs → Dance as bs → Dance as cs
  _⊚_ {as} {bs} {cs} fs gs = record
    { Ds = λ x → IL.Ds fs x ∘ IL.Ds gs x
    ; Es = my-Es
    }
    where
    postulate my-Es : ∀ {x y} → B Base x y → _

  comp3 : ∀ {as bs cs ds} → Dance cs ds → Dance bs cs → Dance as bs → Dance as ds
  comp3 f g h = f ⊚ (g ⊚ h)
