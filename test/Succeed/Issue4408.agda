module Issue4408 where

comp :
  (A : Set)
  (B : A → Set)
  (C : (x : A) → B x → Set) →
  ((x : A) (y : B x) → C x y) →
  (g : (x : A) → B x) →
  ((x : A) → C x (g x))
comp _ _ _ f g x = f x (g x)

data Unit : Set where
  unit : Unit

P : Unit → Set
P unit = Unit

Q : Unit → Set → Set
Q unit = λ _ → Unit

f : (x : Unit) → P x → P x
f unit x = x

g :
  (A : Set) →
  ((x : Unit) → Q x A → P x) →
  ((x : Unit) → Q x A → P x)
g A h x = comp _ _ _ (λ _ → f _) (h _)
