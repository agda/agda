module 14-implicitConfigurations where

postulate
  Integral : Set → Set
  add : ∀ {A} {{ intA : Integral A }} → A → A → A
  mul : ∀ {A} {{ intA : Integral A }} → A → A → A
  mod : ∀ {A} {{ intA : Integral A }} → A → A → A
  
  N : Set
  zero one two three : N
  nInt : Integral N

private postulate Token : Set

record Modulus (s : Token) (A : Set) : Set where
  field modulus : A

data M (s : Token) (A : Set) : Set where
  MkM : A → M s A

unMkM : ∀ {A s} → M s A → A
unMkM (MkM a) = a

private postulate theOnlyToken : Token

withModulus :
  ∀ {A} → {{ intA : Integral A }} → (modulus : A) →
  (∀ {s} → {{ mod : Modulus s A }} → M s A) → A
withModulus modulus f = unMkM
  (f {theOnlyToken} {{  record { modulus = modulus }  }})

open Modulus {{...}}

normalize : ∀ {s A} {{intA : Integral A}} {{mod : Modulus s A}} → 
            A → M s A
normalize a = MkM (mod modulus a)

_+_ : ∀ {s A} {{intA : Integral A}} {{mod : Modulus s A}} → 
      M s A → M s A → M s A
(MkM a) + (MkM b) = normalize (add a b)

_*_ : ∀ {s A} → {{intA : Integral A}} → {{mod : Modulus s A}} → 
      M s A → M s A → M s A
(MkM a) * (MkM b) = normalize (mul a b)

test₁ : N
test₁ = withModulus two (let o = MkM one in (o + o)*(o + o))

testExpr : ∀ {s} → {{mod : Modulus s N}} → M s N
testExpr = let o = MkM one ; t = MkM two in 
           (o + t) * t

test₂ : N
test₂ = withModulus three testExpr
