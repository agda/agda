
module DefinitionalEquality where

postulate
  _≡_      : {A B : Set} -> A -> B -> Set
  refl-≡   : {A : Set}{x : A} -> x ≡ x
  subst-≡  : {A : Set}{x y : A}(C : A -> Set) -> x ≡ y -> C y -> C x
  subst-≡¹ : {A : Set}{x y : A}(C : A -> Set1) -> x ≡ y -> C y -> C x

  subst-≡' : {A B : Set}{x : A}{y : B}(C : {X : Set} -> X -> Set) -> x ≡ y -> C y -> C x

  app-≡₀ : {A₁ A₂ : Set}{B₁ : A₁ -> Set}{B₂ : A₂ -> Set}
           {f : (x : A₁) -> B₁ x}{g : (x : A₂) -> B₂ x}{a₁ : A₁}{a₂ : A₂} ->
            f ≡ g -> a₁ ≡ a₂ -> f a₁ ≡ g a₂

  η-≡ : {A₁ A₂ : Set}{B₁ : A₁ -> Set}{B₂ : A₂ -> Set}
        {f₁ : (x : A₁) -> B₁ x}{f₂ : (x : A₂) -> B₂ x} ->
        ((x : A₁)(y : A₂) -> x ≡ y -> f₁ x ≡ f₂ y) -> f₁ ≡ f₂

  -- Substitution is a no-op
  subst-≡-identity : {A : Set}{x y : A}(C : A -> Set)(p : x ≡ y)(cy : C y) ->
                     subst-≡ C p cy ≡ cy

cong-≡ : {A B : Set}{x y : A}(f : A -> B)(p : x ≡ y) -> f x ≡ f y
cong-≡ {_}{_}{_}{y} f p = subst-≡ (\z -> f z ≡ f y) p refl-≡

cong-≡' : {A : Set}{B : A -> Set}{x y : A}(f : (z : A) -> B z)(p : x ≡ y) -> f x ≡ f y
cong-≡' {_}{_}{_}{y} f p = subst-≡ (\z -> f z ≡ f y) p refl-≡

cong₂-≡' : {A : Set}{B : A -> Set}{C : (x : A) -> B x -> Set}
	   {x y : A}{z : B x}{w : B y}(f : (x : A)(z : B x) -> C x z) ->
	   x ≡ y -> z ≡ w -> f x z ≡ f y w
cong₂-≡' f xy zw = app-≡₀ (cong-≡' f xy) zw

trans-≡ : {A B C : Set}(x : A)(y : B)(z : C) -> x ≡ y -> y ≡ z -> x ≡ z
trans-≡ x y z xy yz = subst-≡' (\w -> w ≡ z) xy yz

postulate
  _≡₁_     : {A B : Set1} -> A -> B -> Set1
  refl-≡₁  : {A : Set1}{x : A} -> x ≡₁ x
  subst-≡₁ : {A : Set1}{x y : A}(C : A -> Set1) -> x ≡₁ y -> C y -> C x
  subst-≡₁' : {A B : Set1}{x : A}{y : B}(C : {X : Set1} -> X -> Set1) -> x ≡₁ y -> C y -> C x

  -- Substitution is a no-op
  subst-≡₁-identity : {A : Set1}{x y : A}(C : A -> Set1)(p : x ≡₁ y)(cy : C y) ->
                      subst-≡₁ C p cy ≡₁ cy

  app-≡₁ : {A₁ A₂ : Set1}{B₁ : A₁ -> Set1}{B₂ : A₂ -> Set1}
           {f : (x : A₁) -> B₁ x}{g : (x : A₂) -> B₂ x}{a₁ : A₁}{a₂ : A₂} ->
           f ≡₁ g -> a₁ ≡₁ a₂ -> f a₁ ≡₁ g a₂

  app-≡₁⁰ : {A₁ A₂ : Set}{B₁ : A₁ -> Set1}{B₂ : A₂ -> Set1}
            {f : (x : A₁) -> B₁ x}{g : (x : A₂) -> B₂ x}{a₁ : A₁}{a₂ : A₂} ->
            f ≡₁ g -> a₁ ≡ a₂ -> f a₁ ≡₁ g a₂

  η-≡₁ : {A₁ A₂ : Set1}{B₁ : A₁ -> Set1}{B₂ : A₂ -> Set1}
         {f₁ : (x : A₁) -> B₁ x}{f₂ : (x : A₂) -> B₂ x} ->
         ((x : A₁)(y : A₂) -> x ≡₁ y -> f₁ x ≡₁ f₂ y) -> f₁ ≡₁ f₂

  η-≡₁⁰ : {A₁ A₂ : Set}{B₁ : A₁ -> Set1}{B₂ : A₂ -> Set1}
          {f₁ : (x : A₁) -> B₁ x}{f₂ : (x : A₂) -> B₂ x} ->
          ((x : A₁)(y : A₂) -> x ≡ y -> f₁ x ≡₁ f₂ y) -> f₁ ≡₁ f₂

cong-≡₁ : {A B : Set1}{x y : A}(f : A -> B)(p : x ≡₁ y) -> f x ≡₁ f y
cong-≡₁ {_}{_}{_}{y} f p = subst-≡₁ (\z -> f z ≡₁ f y) p refl-≡₁

cong-≡₁⁰ : {A : Set}{B : A -> Set1}{x y : A}(f : (x : A) -> B x)(p : x ≡ y) -> f x ≡₁ f y
cong-≡₁⁰ {_}{_}{_}{y} f p = subst-≡¹ (\z -> f z ≡₁ f y) p refl-≡₁

trans-≡₁ : {A B C : Set1}(x : A)(y : B)(z : C) -> x ≡₁ y -> y ≡₁ z -> x ≡₁ z
trans-≡₁ x y z xy yz = subst-≡₁' (\w -> w ≡₁ z) xy yz

