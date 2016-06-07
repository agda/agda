
module _ where

open import Agda.Primitive
open import Agda.Builtin.Nat
open import Agda.Builtin.List
open import Agda.Builtin.Equality

[_==_] : ∀ {a} {A : Set a} (x y : A) → x ≡ y → A
[ x == _ ] _ = x

pattern ! = refl

f : Nat → Nat
f zero      = zero
f n@(suc m) = n

data Vec {a} (A : Set a) : Nat → Set a where
  []  : Vec A zero
  _∷_ : ∀ {n} → A → Vec A n → Vec A (suc n)

_++_ : ∀ {a n m} {A : Set a} → Vec A n → Vec A m → Vec A (n + m)
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

toList : ∀ {a n} {A : Set a} → Vec A n → List A
toList []       = []
toList (x ∷ xs) = x ∷ toList xs

foo : ∀ {a n} {A : Set a} (xs ys : Vec A n) → Vec A (n + n)
foo [] [] = []
foo xs@(x ∷ xs₁) ys@(y ∷ ys₁) = [ xs == x ∷ xs₁ ] ! ++ [ ys == y ∷ ys₁ ] !

--- Record patterns ---

infixr 0 _,_
record Σ {a b} (A : Set a) (B : A → Set b) : Set (a ⊔ b) where
  constructor _,_
  field
    fst : A
    snd : B fst

open Σ

rec : ∀ {a b} {A : Set a} {B : A → Set b} → Σ A B → Σ A B
rec p@record{ fst = x; snd = y } = p

_|>_ : ∀ {a b} {A : Set a} {B : Set b} → A → B → B
_ |> x = x

insideRec : ∀ {a} {A : Set a} → Σ Nat (Vec A) → List A
insideRec p@record{ fst = zero     ; snd = xs  } = toList ([ snd p == xs ] !)
insideRec record { fst = n@(suc _) ; snd = xs@(x ∷ []) } =
  [ n == 1 ] ! |> toList ([ xs == x ∷ [] ] !)
insideRec record { fst = n@(suc _) ; snd = xs₀@(x ∷ xs₁@(x₁ ∷ xs)) } =
  toList ([ xs₀ == x ∷ xs₁ ] ! ++ [ xs₁ == x₁ ∷ xs ] !)

check : insideRec (_ , 1 ∷ 2 ∷ 3 ∷ []) ≡ 1 ∷ 2 ∷ 3 ∷ 2 ∷ 3 ∷ []
check = refl

--- Copatterns ---

Nary : ∀ {a} → Nat → Set a → Set a
Nary zero    A = A
Nary (suc n) A = Nat → Nary n A

copat : ∀ {a} {A : Set a} → (Nat → A) → Σ Nat λ n → Nary n A
fst (copat f) = 1
snd (copat f) n@(suc m) = f ([ n == suc m ] !)
snd (copat f) n@zero    = f ([ n == 0 ] !)

--- Dot patterns ---

weird-but-legal : ∀ n → Vec Nat n → Nat
weird-but-legal n@.n [] = [ n == 0 ] !
weird-but-legal n@.n (_∷_ {m} x xs) = [ n == suc m ] !

--- Let pattern bindings ---

letpat : ∀ {a} {A : Set a} → Σ Nat (Vec A) → Nat
letpat p =
  let q@(n , xs) = p in [ fst ([ p == q ] !) == n ] !

letpat₁ : Σ Nat (λ _ → Σ Nat λ _ → Nat) → Nat
letpat₁ p =
  let (a , q@(b , c)) = p in [ snd q == c ] !
