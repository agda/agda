-- exercises
-- * basic logic properties (implication, and, or, bot, not, forall, exists)
-- * data types
-- * records
-- * non-dep, non-rec, non-indexed case splits
-- * including elimination constants as hints
-- * hidden arguments

open import Auto.Prelude


h0 : (A : Set) → A → A
h0 = {!!}
--h0 = λ A z → z

h1 : (A B : Set) → A → (A → B) → B
h1 = {!!}
--h1 = λ A B z z₁ → z₁ z

h2 : ∀ A B → A ∧ B → B ∧ A
h2 = {!!}
--h2 = λ A B z → ∧-i (_∧_.snd z) (_∧_.fst z)

h3 : ∀ A B C → (A ∧ B) ∧ C → A ∧ (B ∧ C)
h3 = {!!}
--h3 = λ A B C z →
--         ∧-i (_∧_.fst (_∧_.fst z)) (∧-i (_∧_.snd (_∧_.fst z)) (_∧_.snd z))


h4 : (A B C : Set) → A ∨ B → (A → C) → (B → C) → C
h4 A B C x h₁ h₂ = {!-c!}


h5 : ∀ A B → A ∨ B → B ∨ A
h5 A B x = {!-c!}
--h5 A B (∨-i₁ x) = ∨-i₂ x
--h5 A B (∨-i₂ x) = ∨-i₁ x

h6 : ∀ A B C → (A ∨ B) ∨ C → A ∨ (B ∨ C)
h6 A B C x = {!-c!}
--h6 A B C (∨-i₁ (∨-i₁ x)) = ∨-i₁ x
--h6 A B C (∨-i₁ (∨-i₂ x)) = ∨-i₂ (∨-i₁ x)
--h6 A B C (∨-i₂ x) = ∨-i₂ (∨-i₂ x)

h7 : (A : Set) → ⊥ → A
h7 A x = {!-c!}



h8 : ∀ A → A → ¬ (¬ A)
h8 = {!!}
--h8 = λ A z z₁ → z₁ z

h9 : ∀ A → ¬ (¬ (¬ A)) → ¬ A
h9 = {!!}
--h9 = λ A z z₁ → z (λ z₂ → z₂ z₁)

h10 : (∀ A → ¬ (¬ A) → A) →
     (∀ A → A ∨ ¬ A)
h10 = {!!}
--h10 = λ z A →
--         z (A ∨ ((x : A) → ⊥)) (λ z₁ → z₁ (∨-i₂ (λ x → z₁ (∨-i₁ x))))

h11 : (∀ A → A ∨ ¬ A) →
      (∀ A → ¬ (¬ A) → A)
h11 = {!∨-e ⊥-e!}
--h11 = λ z A z₁ →
--          ∨-e A ((x : A) → ⊥) A (z A) (λ z₂ → z₂) (λ z₂ → ⊥-e A (z₁ z₂))


h12 : {X : Set} {P Q : X → Set} → ((x : X) → P x ∧ Q x) → ((x : X) → P x) ∧ ((x : X) → Q x)
h12 = {!!}
--h12 = λ {X} {P} {Q} z → ∧-i (λ x → _∧_.fst (z x)) (λ x → _∧_.snd (z x))

h13 : {X : Set} {P Q : X → Set} → ((x : X) → P x) ∧ ((x : X) → Q x) → ((x : X) → P x ∧ Q x)
h13 = {!!}
--h13 = λ {X} {P} {Q} z x → ∧-i (_∧_.fst z x) (_∧_.snd z x)



n0 : {X : Set} {P Q : X → Set} → Σ X (λ x → P x ∨ Q x) → Σ X P ∨ Σ X Q
--n0 = {!∨-e!}  -- no solution found, not even for the two subproofs
n0 = λ h → ∨-e _ _ _ (Σ.prf h) (λ x → ∨-i₁ (Σ-i (Σ.wit h) x)) (λ x → ∨-i₂ (Σ-i (Σ.wit h) x))

n1 : {X : Set} {P Q : X → Set} → Σ X P ∨ Σ X Q → Σ X (λ x → P x ∨ Q x)
--n1 = {!∨-e!}  -- no solution found, not even for the two subproofs
n1 = λ h → ∨-e _ _ _ h (λ x → Σ-i (Σ.wit x) (∨-i₁ (Σ.prf x))) (λ x → Σ-i (Σ.wit x) (∨-i₂ (Σ.prf x)))

h14 : {X : Set} → (x : X) → Σ X (λ x → ⊤)
h14 = {!!}
--h14 = λ {X} x → Σ-i x (record {})

h15 : {X : Set} → Σ (X → X) (λ x → ⊤)
h15 = {!!}
--h15 = λ {X} → Σ-i (λ x → x) (record {})

h16 : {X : Set} {P : X → Set} → Σ (X → X) (λ f → (x : X) → P (f x) → P x)
h16 = {!!}
--h16 = λ {X} {P} → Σ-i (λ x → x) (λ x x₁ → x₁)

module Drink where

 postulate RAA : (A : Set) → (¬ A → ⊥) → A

 drink : (A : Set) → (a : A)
            → (Drink : A → Set) → Σ A (λ x → (Drink x) → Π A Drink)
 drink A a Drink = {!RAA!}  -- h17
{-
 drink A a Drink = RAA (Σ A (λ z → (x : Drink z) → Π A Drink))
                     (λ z →
                        z
                        (Σ-i a
                         (λ x →
                            fun
                            (λ a₁ →
                               RAA (Drink a₁)
                               (λ z₁ →
                                  z (Σ-i a₁ (λ x₁ → fun (λ a₂ → RAA (Drink a₂) (λ _ → z₁ x₁)))))))))  -- h17
-}
