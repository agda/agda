
open import Common.Prelude
open import Common.Reflection
open import Common.Equality

tt : ⊤
tt = record{}

arg₀ : {A : Set} → A → Arg A
arg₀ = arg (argInfo visible relevant)

el₀ : Term → Type
el₀ = el (lit 0)

NoConf : Nat → Nat → Set
NoConf zero zero = ⊤
NoConf zero (suc n) = ⊥
NoConf (suc m) zero = ⊥
NoConf (suc m) (suc n) = m ≡ n

-- noConf : (m n : ℕ) → m ≡ n → NoConfusion-ℕ m n
-- noConf zero .zero refl = tt
-- noConf (suc m) .(suc m) refl = refl

noConf : FunDef
noConf = funDef
  (el₀ (pi (arg₀ (el₀ (def (quote Nat) [])))
   (abs "_"
    (el₀ (pi (arg₀ (el₀ (def (quote Nat) [])))
     (abs "_"
      (el₀ (pi (arg₀ (el₀ (def (quote _≡_) (arg₀ (var 1 []) ∷ arg₀ (var 0 []) ∷ []))))
       (abs "_"
        (el₀ (def (quote NoConf) (arg₀ (var 2 []) ∷ arg₀ (var 1 []) ∷ []))))))))))))
  ( clause (arg₀ (con (quote zero) []) ∷ arg₀ dot ∷ arg₀ (con (quote refl) []) ∷ [])
           (def (quote tt) [])
  ∷ clause (arg₀ (con (quote suc) (arg₀ (var "m") ∷ [])) ∷ arg₀ dot ∷ arg₀ (con (quote refl) []) ∷ [])
           (def (quote refl) [])
  ∷ [])

unquoteDecl test = noConf
