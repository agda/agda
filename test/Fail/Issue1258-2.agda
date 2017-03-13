module Issue1258-2 where

data Nat : Set where
    zero : Nat
    suc  : Nat -> Nat

data _==_ {A : Set}(x : A) : A -> Set where
  refl : x == x

data Bool : Set where
  true false : Bool

data Σ (A : Set) (B : A → Set) : Set where
  _,_ : (x : A) → B x → Σ A B

_×_ : Set → Set → Set
A × B = Σ A (λ _ → B)

postulate f : (A : Set) -> A -> Bool

record Wrap (A : Set) : Set where
  constructor wrap
  field wrapped : A

data ⊥ : Set where

Foo : Bool -> Set
Foo true  = ⊥
Foo false = ⊥

Alpha : Bool
Stuck = Foo Alpha
Beta : Stuck

test : f (Bool × Wrap Nat) (true , wrap zero) == f (Stuck × Stuck) (Beta , Beta)
Alpha = _
Beta  = _
test  = refl
