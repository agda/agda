
id : forall {k}{X : Set k} -> X -> X
id x = x

_o_ : forall {i j k}
  {A : Set i}{B : A -> Set j}{C : (a : A) -> B a -> Set k} ->
  (f : {a : A}(b : B a) -> C a b) ->
  (g : (a : A) -> B a) ->
  (a : A) -> C a (g a)
f o g = \ a -> f (g a)

data List (X : Set) : Set where
  [] : List X
  _,_ : X → List X → List X

data Nat : Set where
  zero : Nat
  suc : Nat → Nat

{-# BUILTIN NATURAL Nat #-}

data Vec (X : Set) : Nat -> Set where
  [] : Vec X 0
  _,_ : { n : Nat } → X → Vec X n → Vec X (suc n)

vec : forall { n X } → X → Vec X n
vec {zero} a = []
vec {suc n} a = a , vec a

vapp : forall { n S T } → Vec (S → T) n → Vec S n → Vec T n
vapp [] [] = []
vapp (x , st) (x₁ , s) = x x₁ , vapp st s

record Applicative (F : Set → Set) : Set₁ where
  infixl 2 _⊛_
  field
    pure : forall { X } → X → F X
    _⊛_ : forall { S T } → F (S → T) → F S → F T

open Applicative {{...}} public

instance
  applicativeVec : forall { n } → Applicative (λ X → Vec X n)
  applicativeVec = record { pure = vec; _⊛_ = vapp }

instance
  applicativeComp : forall {F G} {{_ : Applicative F}} {{_ : Applicative G}} → Applicative (F o G)
  applicativeComp {{af}} {{ag}} =
    record
    { pure = λ z → Applicative.pure af (Applicative.pure ag z)
    ; _⊛_ = λ z → {!!}
    }

record Traversable (T : Set → Set) : Set1 where
  field
    traverse : forall { F A B } {{ AF : Applicative F }} → (A → F B) → T A → F (T B)

open Traversable {{...}} public

instance
  traversableVec : forall {n} → Traversable (\X → Vec X n)
  traversableVec = record { traverse = vtr } where
    vtr : forall { n F A B } {{ AF : Applicative F }} → (A → F B) → Vec A n → F (Vec B n)
    vtr {{AF}} f [] = Applicative.pure AF []
    vtr {{AF}} f (x , v) =
      Applicative._⊛_ AF (Applicative._⊛_ AF (Applicative.pure AF _,_) (f x)) (vtr f v)
