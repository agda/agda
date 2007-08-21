
module Bool where

data Bool : Set where
  false : Bool
  true  : Bool

data IsTrue : Bool -> Set where
  isTrue : IsTrue true

open import Vec
open import All

allEnvs : {n : Nat} -> List (Vec Bool n)
allEnvs {zero } = ε :: []
allEnvs {suc n} = map (_►_ false) allEnvs ++ map (_►_ true) allEnvs

∈++left : {A : Set}{x : A}{xs ys : List A} -> x ∈ xs -> x ∈ (xs ++ ys)
∈++left (hd p) = hd p
∈++left (tl q) = tl (∈++left q)

∈++right : {A : Set}{x : A}{xs ys : List A} -> x ∈ ys -> x ∈ (xs ++ ys)
∈++right {xs = []}      p = p
∈++right {xs = x :: xs} p = tl (∈++right {xs = xs} p)

∈map : {A B : Set}{f : A -> B}{x : A}{xs : List A} -> x ∈ xs -> f x ∈ map f xs
∈map (hd refl) = hd refl
∈map (tl q)    = tl (∈map q)

covered : {n : Nat} -> (xs : Vec Bool n) -> xs ∈ allEnvs
covered ε            = hd refl
covered (false ► xs) = ∈++left (∈map (covered xs))
covered (true  ► xs) = ∈++right {xs = map (_►_ false) allEnvs}
                                (∈map (covered xs))

Sat : {A : Set} -> (A -> Bool) -> A -> Set
Sat f x = IsTrue (f x)

lem₁ : {n : Nat}(f : Vec Bool n -> Bool) ->
      All (Sat f) allEnvs -> (xs : Vec Bool n) -> Sat f xs
lem₁ f p xs with p ! covered xs
... | (.xs , p , refl) = p

data False : Set where

¬_ : Set -> Set
¬ P = P -> False

data _∨_ (A B : Set) : Set where
  inl : A -> A ∨ B
  inr : B -> A ∨ B

¬IsTrue-false : ¬ IsTrue false
¬IsTrue-false ()

decide : {A : Set}(p : A -> Bool)(x : A) ->
         Sat p x ∨ ¬ Sat p x
decide p x with p x
... | true  = inl isTrue
... | false = inr ¬IsTrue-false

all : {A : Set}(p : A -> Bool)(xs : List A) ->
      All (Sat p) xs ∨ Some (\x -> ¬ Sat p x) xs
all p [] = inl ∅
all p (x :: xs) with decide p x
... | inr ¬px = inr (hd ¬px)
... | inl px  with all p xs
...   | inl ps = inl (px ▹ ps)
...   | inr q  = inr (tl q)

data NoProof : Set where
  no-proof : NoProof

Proof : {n : Nat} -> (Vec Bool n -> Bool) -> Set
Proof {n} f with all f allEnvs
... | inl _ = (xs : Vec Bool n) -> Sat f xs
... | inr _ = NoProof

prove : {n : Nat}(f : Vec Bool n -> Bool) -> Proof f
prove f with all f allEnvs
... | inl ps = lem₁ f ps
... | inr _  = no-proof
