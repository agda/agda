{-# OPTIONS --rewriting --local-rewriting -WnoRewriteVariablesBoundInSingleton #-}

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

module LocalRewriteExt where

variable
  A B : Set
  x y : A

postulate
  I     : Set
  i0 i1 : I
  ~_    : I → I
  ~0    : ~ i0 ≡ i1
  ~1    : ~ i1 ≡ i0

{-# REWRITE ~0 ~1 #-}

postulate
  Path : (A : Set) → A → A → Set

postulate
  fromPath : Path A x y → I → A

  fromPath0 : {p : Path A x y} → fromPath p i0 ≡ x
  fromPath1 : {p : Path A x y} → fromPath p i1 ≡ y

module _ {A : Set} (f : I → A) {x y : A}
         (@rew f0 : f i0 ≡ x) (@rew f1 : f i1 ≡ y) where
  postulate
    toPath : Path A x y

    fromTo : fromPath toPath ≡ f

{-# REWRITE fromPath0 fromPath1 #-}

postulate
  toFrom : {p : Path A x y} → toPath (fromPath p) refl refl ≡ p

{-# REWRITE fromTo toFrom #-}

sym : Path A x y → Path A y x
sym p = toPath (λ i → fromPath p (~ i)) refl refl

ap : (f : A → B) → Path A x y → Path B (f x) (f y)
ap f p = toPath (λ i → f (fromPath p i)) refl refl
