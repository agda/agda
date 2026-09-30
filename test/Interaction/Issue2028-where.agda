-- Testcase for #2028 by Ulf

record ⊤ : Set where
  constructor tt

data Either (A B : Set) : Set where
  inl : A → Either A B
  inr : B → Either A B

Subset : Set → Set₁
Subset X = X → Set

U : ∀ {X} → Subset X
U _ = {!⊤!}

_⊆_ : ∀ {X} → Subset X → Subset X → Set
A ⊆ B = ∀ {x} → A x → B x

_∪_ : ∀ {X} → Subset X → Subset X → Subset X
(A ∪ B) x = Either (A x) (B x)

∪-bound : ∀ {X} {A : Subset X} → (A ∪ U) ⊆ U
∪-bound {X} {A} = aux
  where
    aux : _ → _
    aux (inl _) = tt
    aux (inr tt) = tt
