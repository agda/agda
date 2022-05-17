-- {-# OPTIONS --no-forcing #-}
{-# OPTIONS --rewriting #-}
{-# OPTIONS --sized-types #-}

open import Agda.Builtin.Equality
open import Agda.Builtin.Size

{-# BUILTIN REWRITE _≡_ #-}

variable i j : Size

postulate ANY : ∀{A : Set} → A

data Ty : Set where
  bool : Ty

variable a b c d : Ty

infixl 5 _∘_
infixr 6 _∷_ _++_

mutual

  data Tm (c : Ty) : Set where
    tm : ∀{i a} (E : Stack i a c) → Tm c

  data Stack (i : Size) : (a c : Ty) → Set where
    ε    : ∀{c} → Stack i c c
    _∷_  : ∀{j : Size< i}{b} (u : Tm b) (E : Stack j b c) → Stack i bool c

  variable E E' E′ : Stack i a c

_++_ : ∀{a b c} → Stack ∞ a b → Stack ∞ b c → Stack ∞ a c
ε       ++ E′ = E′
(u ∷ E) ++ E′ = u ∷ (E ++ E′)

postulate
  _∘_ : ∀{i a c} → Tm a → Stack i a c → Tm c
  app-app : ∀{i j a b c}{t : Tm a} {E : Stack i a b} {E′ : Stack j b c} → t ∘ E ∘ E′ ≡ t ∘ E ++ E′

{-# REWRITE app-app #-}

infix 4 _↦_  _↦ₛ_

mutual

  data _↦_ {c} : (t t′ : Tm c) → Set where
    ↦E  : (r : E ↦ₛ E′) → tm E ↦ tm E′
    -- ↦E  : ∀{i a} {E E′ : Stack i a c} (r : E ↦ₛ E′) → tm E ↦ tm E′ -- no internal error

  data _↦ₛ_ {c} : ∀ {i a} (E E′ : Stack i a c) → Set where
    π     : ∀{i a u v} {E : Stack i a c} → (u ∷ v ∷ E) ↦ₛ ((u ∘ v ∷ ε) ∷ E)
    there : ∀{i a u} {E E′ : Stack i a c} (r : E ↦ₛ E′) → u ∷ E ↦ₛ u  ∷ E′

data SN {a} (t : Tm a) : Set where
  acc : (h : {t′ : Tm a} (r : t ↦ t′) → SN t′) → SN t

-- {-# TERMINATING #-}  -- removes internal error

test : {i : Size} {a c : Ty} {t : Tm a} {E : Stack i a c}
          (sntE : SN (t ∘ E))
          → SN (tm (t ∷ E))
test {i = i} {t = t} (acc sntE) = acc
  λ { (↦E (there r)) → test (sntE ANY)
    ; (↦E (π {i = j})) → test {i = j} (acc sntE)
    }
