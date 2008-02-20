{-

    TBA - Talk 'Bout Agda

    Ulf Norell
    Chalmers

    DTP 2008, Nottingham

-}
module Talk where

-- Normal everyday lists

data List (A : Set) : Set where
  []   : List A
  _::_ : A -> List A -> List A

infixr 40 _::_

map : {A B : Set} -> (A -> B) -> List A -> List B
map f []        = []
map f (x :: xs) = f x :: map f xs

-- More boring types: Bool and Maybe

data Bool : Set where
  false : Bool
  true  : Bool

data Maybe (A : Set) : Set where
  nothing : Maybe A
  just    : A -> Maybe A

fmap : forall {A B} -> (A -> B) -> Maybe A -> Maybe B
fmap f nothing  = nothing
fmap f (just x) = just (f x)

-- The intensional equality type

data _==_ {A : Set}(x : A) : A -> Set where
  refl : x == x

-- Sigma types

data Σ {A : Set}(B : A -> Set) : Set where
  _,_ : (x : A) -> B x -> Σ B

fst : {A : Set}{B : A -> Set} -> Σ B -> A
fst (x , y) = x

snd : {A : Set}{B : A -> Set}(p : Σ B) -> B (fst p)
snd (x , y) = y

_×_ : Set -> Set -> Set
A × B = Σ {A} (\_ -> B)

-- A more interesting type

infix 20 _∈_
data _∈_ {A : Set} : A -> List A -> Set where
  first : forall {x xs} -> x ∈ x :: xs
  later : forall {x y xs} -> x ∈ xs -> x ∈ y :: xs

module Map (K V : Set)
           (_=?=_ : (x y : K) -> Maybe (x == y))
    where

  Map : Set
  Map = List (K × V)

  HasKey : K -> Map -> Set
  HasKey k m = k ∈ map fst m

  member : (x : K)(m : Map) -> Maybe (HasKey x m)
  member x [] = nothing
  member x ((y , v) :: m) with x =?= y
  ... | nothing   = fmap later (member x m)
  member x ((.x , v) :: m) | just refl = just first

  lookup : (x : K)(m : Map) -> HasKey x m -> Σ \v -> (x , v) ∈ m
  lookup x []              ()
  lookup x ((.x , u) :: m)  first    = u , first
  lookup x (e        :: m) (later p) with lookup x m p
  ... | v , q = v , later q
