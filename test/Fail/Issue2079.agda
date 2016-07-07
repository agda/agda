
data Cx (U : Set) : Set where
  ∅   : Cx U
  _,_ : Cx U → U → Cx U

data _∈_ {U : Set} (A : U) : Cx U → Set where
  top : ∀ {Γ} → A ∈ (Γ , A)
  pop : ∀ {B Γ} → A ∈ Γ → A ∈ (Γ , B)

infixr 3 _⇒_
data Ty : Set where
  ι   : Ty
  _⇒_ : Ty → Ty → Ty
  □_  : Ty → Ty

infix 1 _⊢_
data _⊢_ : Cx Ty → Ty → Set where
  var  : ∀ {Γ A}     → A ∈ Γ → Γ ⊢ A
  app  : ∀ {Γ A B}   → Γ ⊢ A ⇒ B → Γ ⊢ A → Γ ⊢ B
  nec  : ∀ {A}       → ∅ ⊢ A → ∅ ⊢ □ A
  kcom : ∀ {Γ A B}   → Γ ⊢ A ⇒ B ⇒ A
  scom : ∀ {Γ A B C} → Γ ⊢ (A ⇒ B ⇒ C) ⇒ (A ⇒ B) ⇒ A ⇒ C
  dist : ∀ {Γ A B}   → Γ ⊢ □ (A ⇒ B) ⇒ □ A ⇒ □ B
  down : ∀ {Γ A}     → Γ ⊢ □ A ⇒ A
  up   : ∀ {Γ A}     → Γ ⊢ □ A ⇒ □ □ A

icom : ∀ {A Γ} → Γ ⊢ A ⇒ A
icom {A} = app (app (scom {A = A} {B = A ⇒ A} {C = A}) kcom) kcom

ded : ∀ {A B Γ} → Γ , A ⊢ B → Γ ⊢ A ⇒ B
ded (var top)     = icom
ded (var (pop i)) = app kcom (var i)
ded (app t u)     = app (app scom (ded t)) (ded u)
ded (nec t)       = ?
ded kcom          = app kcom kcom
ded scom          = app kcom scom
ded dist          = app kcom dist
ded down          = app kcom down
ded up            = app kcom up
