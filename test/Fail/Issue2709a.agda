
open import Agda.Primitive

data   A : Set₁ where mkA : A
record B : Set₁ where field prj : Set

record T (I : Set₁) (i : I) (f : I → Set) (C : Set) : Set₁ where
  field unsingleton : Set

postulate
  P : (I : Set₁) → (I → Set) → Set

it : {A : Set₁} {{x : A}} → A
it {{x}} = x

mutual
  -- Dummy meta to prevent solutions.
  ?X : Set
  ?X = _

  ?B : Set → Set₁
  ?B = _

  ?g : ?B ?X → Set
  ?g = _

  ?f : A → Set
  ?f = _

  -- adds constraint A == ?B ?X
  -- and solves ?f := ?g
  constr₁ : P A ?f → P (?B ?X) ?g
  constr₁ x = x

  -- This crashes if ?f == B.prj.
  -- It's convenient to make it an instance goal since
  -- instance search first tries to eta expand the goal,
  -- triggering the crash in this case. There are probably
  -- other ways of triggering eta expansion of an ill-typed
  -- meta though.
  constr₂ : T A mkA ?f (?f mkA)
  constr₂ = it

  -- solves ?B := λ _ → B
  -- and    ?g := B.prj
  solve : ∀ {X} → (?B X → P (?B ?X) ?g) → B → P B B.prj
  solve f = f
