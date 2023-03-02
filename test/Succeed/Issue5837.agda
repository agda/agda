open import Agda.Builtin.Bool
open import Agda.Builtin.Unit
open import Agda.Builtin.Equality

module _ where

module Test1 where

  postulate
    F : Set → ⊤
    G : ⊤ → Set

  mutual
    X : Set
    X = _

    solve : {Y : Set} → X ≡ G (F Y)
    solve = refl

  {- WAS:
  Cannot instantiate the metavariable _5 to solution G (F Y)
  since it contains the variable Y
  which is not in scope of the metavariable
  when checking that the expression refl has type X ≡ G (F Y)
  -}

module Test2 where

  data ⊥ : Set where

  T : Bool → Set
  T true  = ⊤
  T false = ⊥

  postulate
    F : ⊤ → Set

  mutual
    X : Set
    X = _

    solve : {Y : (b : Bool) → T b} → X ≡ F (Y true)
    solve = refl

  {- WAS:
  Cannot instantiate the metavariable _8 to solution F (Y true)
  since it contains the variable Y
  which is not in scope of the metavariable
  when checking that the expression refl has type X ≡ F (Y true)
  -}

module Test3 where

  data D (A : Set) : Set₁ where
    c : ((Set → A) → A) → D A

  mutual
    x : D ⊤
    x = _

    solve : {Y : Set} → x ≡ c (λ G → G Y)
    solve = refl

  {- WAS:
  Cannot instantiate the metavariable _8 to solution c (λ G → G Y)
  since it contains the variable Y
  which is not in scope of the metavariable
  when checking that the expression refl has type x ≡ c (λ G → G Y)
  -}
