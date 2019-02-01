
open import Common.Prelude

data Wrap (A : Set) : Set where wrap : A → Wrap A

appWrap : ∀ {A B : Set} → (A → B) → Wrap A → B
appWrap f (wrap a) = f a

app : ∀ {A B : Set} → (A → B) → A → B
app f a = appWrap f (wrap a)

works : Nat
works = (λ _ → 42) ((λ _ → tt) 13)

-- (λ _ → tt) is erased but `app` tries to apply it
buggy : Nat
buggy = app (λ _ → 42) (app (λ _ → tt) 13)

main : IO ⊤
main = printNat buggy
