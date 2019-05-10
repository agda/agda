{-# OPTIONS --rewriting --confluence-check #-}

--{-# OPTIONS -v rewriting:100 #-}

postulate
  _↦_ : ∀ {i} {A : Set i} → A → A → Set i
{-# BUILTIN REWRITE _↦_ #-}

data _==_ {i} {A : Set i} (a : A) : A → Set i where
  idp : a == a

ap : ∀ i j (A : Set i) (B : Set j) (f : A → B) (x y : A)
  → (x == y → f x == f y)
ap _ _ _ _ f _ ._ idp = idp

postulate
  ap∘-rewr : ∀ {i j k} {A : Set i} {B : Set j} {C : Set k} (g : B → C) (f : A → B)
    {x y : A} (p : x == y) →
    ap j k B C g (f x) (f y) (ap i j A B f x y p) ↦ ap i k A C (λ x → g (f x)) x y p
{-# REWRITE ap∘-rewr #-}

-- This one works, rewriting the RHS to the LHS using the previous rewrite rule as expected
{-ap∘ : ∀ {i j k} {A : Set i} {B : Set j} {C : Set k} (g : B → C) (f : A → B)
  {x y : A} (p : x == y) →
  ap (λ x → g (f x)) p == ap g (ap f p)
ap∘ g f p = idp
-}

postulate P : ∀ i (A : Set i) (x y : A) (p : x == y) → Set

-- This one doesn’t work, although it should just have to rewrite [P (ap g (ap f p))] to [P (ap (λ x → g (f x)) p)]
test : ∀ {i j k} {A : Set i} {B : Set j} {C : Set k} (g : B → C) (f : A → B)
  {x y : A} (p : x == y)
  → P k C (g (f x)) (g (f y)) (ap i k A C (λ x → g (f x)) x y p) → P k C (g (f x)) (g (f y)) (ap j k B C g (f x) (f y) (ap i j A B f x y p))
test g f p s = s

{-
.i != .j of type .Agda.Primitive.Level
when checking that the expression s has type P (ap g (ap f p))
-}
