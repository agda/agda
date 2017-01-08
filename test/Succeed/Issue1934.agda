{-# OPTIONS --allow-unsolved-metas #-}

data _≡_ {a} {A : Set a} (x : A) : A → Set a where
  refl : x ≡ x
infix 0 _≡_

{-# BUILTIN EQUALITY _≡_ #-}

data Sigma {l} (A : Set l) (B : A -> Set l) : Set l where
  _**_ : (a : A) -> B a -> Sigma A B

sym : ∀ {a} {A : Set a} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : ∀ {a} {A : Set a} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl eq = eq

subst : ∀ {a b} {x y : Set a} → (P : Set a → Set b) → x ≡ y → P x ≡ P y
subst P refl = refl

cong : ∀ {a b} {A : Set a} {B : Set b} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl
fst : ∀ {l} -> {A : Set l}{B : A -> Set l} -> Sigma A B -> A
fst (x ** _) = x

snd : ∀ {l} -> {A : Set l}{B : A -> Set l} -> (sum : Sigma A B) -> B (fst sum)
snd (x ** y) = y

record Group {l} (G : Set l) (_op_ : G -> G -> G) : Set l where
  field
    assoc : {a b c : G} -> ((a op b) op c) ≡ (a op (b op c))
    id : {a : G} -> Sigma G (\e -> e op a ≡ a)
    inv : {a : G} -> Sigma G (\a^-1 -> (a^-1 op a) ≡ (fst (id {a})))
  e : {a : G} -> G
  e {a} = fst (id {a})

  _^-1 : G -> G
  x ^-1 = fst (inv {x})

  a^-1-op-a==e : {a : G} -> ((a ^-1) op a) ≡ e {a}
  a^-1-op-a==e {a} with inv {a}
  ...                   | (_ ** p) = p

  id-lem-right : {a : G} -> (e {a} op a) ≡ a
  id-lem-right {a} = snd (id {a})

  id-lem-left : {a : G} -> (a op e {a}) ≡ a
  id-lem-left {a} rewrite id-lem-right {a} = {!!}

-- In Agda 2.4.2.5 the error was:

-- Function does not accept argument {r = _}
-- when checking that {r = a} is a valid argument to a function of
-- type {a : G} → G
