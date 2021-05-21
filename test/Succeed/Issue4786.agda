data D (A : Set) : Set where
  c₁ : D A

_ : (@0 A : Set) → D A
_ = λ A → c₁ {A = A}

_ : (@0 A : Set) → D A
_ = λ A → D.c₁ {A = A}

record R (A : Set) : Set where
  constructor c₂
  field
    f : A → A

  g : A → A
  g x = f (f x)

open R public

_ : (@0 A : Set) → (A → A) → R A
_ = λ A → c₂ {A = A}

_ : (@0 A : Set) → R A → A → A
_ = λ A → f {A = A}

_ : (@0 A : Set) → R A → A → A
_ = λ A → R.f {A = A}

_ : (A : Set) → R A → A → A
_ = λ A → g {A = A}

_ : (A : Set) → R A → A → A
_ = λ A → R.g {A = A}

open module R′ (A : Set) (r : R A) = R {A = A} r
  renaming (f to f′; g to g′)

_ : (A : Set) → R A → A → A
_ = λ A → f′ {A = A}

_ : (A : Set) → R A → A → A
_ = λ A → R′.f {A = A}

_ : (A : Set) → R A → A → A
_ = λ A → g′ A

_ : (A : Set) → R A → A → A
_ = λ A → R′.g A
