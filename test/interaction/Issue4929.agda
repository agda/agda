
postulate
  ANY : ∀{a}{A : Set a} → A

data Ty : Set where
  _⇒_ : (a b : Ty) → Ty

data Tm : (b : Ty) → Set where
  S   : ∀{c a b} → Tm ((c ⇒ (a ⇒ b)) ⇒ ((c ⇒ a) ⇒ (c ⇒ b)))
  _∙_ : ∀{a b} (t : Tm (a ⇒ b)) (u : Tm a) → Tm b

data _↦_ : ∀{a} (t t' : Tm a) → Set where

  ↦S : ∀{c a b} {t : Tm (c ⇒ (a ⇒ b))} {u : Tm (c ⇒ a)} {v : Tm c}
     → (((S ∙ t) ∙ u) ∙ v) ↦ ((t ∙ v) ∙ (u ∙ v))

  ↦r : ∀{a b} {u u' : Tm a} {t : Tm (a ⇒ b)}
     → (t ∙ u) ↦ (t ∙ u')

data SN {a} (t : Tm a) : Set where
  acc : (h : ∀{t'} (r : t ↦ t') → SN t') → SN t

test : ∀{a b} {t : Tm (a ⇒ b)} {u : Tm a} → SN t → SN u → SN (t ∙ u)
test snt snu = acc λ{ (↦S) → ANY ; (↦r) → {!test snt ?!} }

  -- Refine with (test snt)
  -- or give (test snt ?)

-- An internal error has occurred. Please report this as a bug.
-- Location of the error: src/full/Agda/TypeChecking/Substitute.hs:456
