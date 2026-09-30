
postulate A : Set
variable  a : A

postulate B : A → Set
variable  b : B a

postulate C : B a → Set
variable  c : C b

postulate
  _==_  : {b b' : B a} → C b → C b' → Set
  _=='_ : {b : B a} → C b → C b → Set

postulate
  f : (b : B a) (b' : B {!a!}) → Set
  g : (c : C b) (c' : C {!b!}) → c == c' → Set

module _ (X : Set) where
  postulate
    h : (b' : B a) (c : C b) (c' : C b') → {!c'!} ==' c' → Set
