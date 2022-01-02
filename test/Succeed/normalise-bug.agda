open import Agda.Builtin.Reflection renaming (bindTC to _>>=_)
open import Agda.Builtin.Sigma
open import Agda.Builtin.List
open import Agda.Builtin.Unit
open import Agda.Builtin.Nat
open import Agda.Builtin.Equality

infixr 0 _$_
_$_ : ∀ {a b}{A : Set a}{B : Set b} → (A → B) → (A → B)
f $ x = f x

map : {A B : Set} → (A → B) → List A → List B
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

reverseAcc : {A : Set} → List A → List A → List A
reverseAcc [] ys = ys
reverseAcc (x ∷ xs) ys = reverseAcc xs (x ∷ ys)

reverse : {A : Set} → List A → List A
reverse xs = reverseAcc xs []

data Vec (A : Set) : Nat → Set where
  []  : Vec A 0
  _∷_ : ∀ {n} (x : A) (xs : Vec A n) → Vec A (suc n)


macro
  ntest : Name → Term → TC ⊤
  ntest f a = do
     (function te@(clause tel _ t ∷ [])) ← withReconstructed $ getDefinition f where
        _ → typeError $ strErr "ERROR" ∷ []
     t ← withReconstructed $ inContext (reverse tel) $ normalise t
     quoteTC t >>= unify a

-- A record with parameters.
record X {n} (x : Vec Nat n) : Set where
  constructor mk
  field
    c : Nat

-- A function that we will call at the unknown argument position
-- when defining the type of `f`.
[_] : ∀ {X} → X → Vec X 1
[ x ] = x ∷ []

-- The function that has two reconstructable arguments in the body.
f : X [ 1 ]
f = mk 1

-- Normalisation of the body of the function should also
-- normalise reconstructed arguments.
test : ntest f ≡ con (quote mk) (_ ∷ arg _ (con (quote Vec._∷_) _) ∷ _)
test = refl
