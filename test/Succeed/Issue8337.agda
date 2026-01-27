module Issue8337 where

record Inner (A : Set) : Set where
  field inner : A
open Inner {{...}}

record Outer (A : Set) : Set where
  field {{outer}} : Inner A
open Outer {{...}}

module InstanceFieldUnderImplicit
    (I : Set) (F : I → Set) {{o : ∀ {i} → Outer (F i)}} where
  test : ∀ {i} → F i
  test = inner

module InstanceFieldUnderInstance
    (I : Set) (F : I → Set) {{o : ∀ {{i : I}} → Outer (F i)}} where
  test : {{i : I}} → F i
  test = inner

module InstanceFieldUnderTwoImplicits
    (I : Set) (J : Set) (F : I → J → Set)
    {{o : ∀ {i} {j} → Outer (F i j)}} where
  test : ∀ {i} {j} → F i j
  test = inner

record MoreOuter (A : Set) : Set where
  field {{moreOuter}} : Outer A
open MoreOuter {{...}}

module InstanceFieldOfInstanceFieldUnderImplicit
    (I : Set) (F : I → Set) {{m : ∀ {i} → MoreOuter (F i)}} where
  test : ∀ {i} → F i
  test = inner

module InstanceFieldUnderExplicit
    (X : Set) (F : X → Set) (G : (x : X) → Outer (F x)) where
  test : ∀ x → F x
  test x = inner

module InstanceFieldUnderExplicitAndInstance
    (X : Set) (Y : Set) {{_ : Inner Y}} (F : X → Set) (G : (x : X) → {{Inner Y}} -> Outer (F x)) where
  test : ∀ x → F x
  test x = inner

module SlightlyPracticalCase where

    data _≡_ {A : Set} (a : A) : A -> Set where
        refl : a ≡ a

    ÷_ : ∀ {A : Set} {a1 a2 : A} -> (a1 ≡ a2) -> (a2 ≡ a1)
    ÷ refl = refl

    record Mul (A : Set) : Set where
      field
        _*_ : A → A → A
    open Mul ⦃ ... ⦄

    record Semimonoid : Set₁ where
      field
        carrier : Set
        ⦃ g ⦄   : Mul carrier
        right-assoc : ∀ (x y z : carrier) -> ((x * y) * z) ≡ (x * (y * z))
    open Semimonoid

    left-assoc : (M : Semimonoid) (x y z : M .carrier) → (x * (y * z)) ≡ ((x * y) * z)
    left-assoc M x y z = ÷ (right-assoc M x y z)
