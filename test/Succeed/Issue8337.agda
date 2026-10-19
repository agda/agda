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
