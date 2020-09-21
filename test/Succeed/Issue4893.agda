open import Agda.Primitive

variable
  ℓ : Level
  A : Set ℓ
  P : A → Set ℓ
  f : (x : A) → P x

postulate
  R : (a : Level) → Set (lsuc a)
  r : (a : Level) → R a

  Id : (a : Level) (A : Set a) → A → A → Set a
  cong₂ : (a b c : Level) (A : Set a) (B : Set b) (C : Set c) (x y : A) (u v : B)
          (f : A → B → C) → Id c C (f x u) (f y v)

  foo   : (x y u v : A) (g : A → A) →
          let a = _ in
          Id a (Id _ _ _ _)
               (cong₂ _ _ _ _ _ _ x y u v (λ x → f (g x)))
               (cong₂ _ _ _ _ _ _ (g x) (g y) u v f)
