-- Giving /lift \phi/ the the first hole TWICE (the first time you get an type error), causes the following internal error:

--   An internal error has occurred. Please report this as a bug.
--   Location of the error:
--   src/full/Agda/TypeChecking/Reduce/Monad.hs:118

------------------------------------------------------------------------
-- Library

infixr 9 _∘_

_∘_ : ∀ {a b c}
        {A : Set a} {B : A → Set b} {C : {x : A} → B x → Set c} →
        (∀ {x} (y : B x) → C y) → (g : (x : A) → B x) →
        ((x : A) → C (g x))
f ∘ g = λ x → f (g x)

data ⊥ : Set where

data _⊎_ (A : Set) (B : Set) : Set where
  inj₁ : (x : A) → A ⊎ B
  inj₂ : (y : B) → A ⊎ B

[_,_] : ∀ {A : Set} {B : Set} {C : A ⊎ B → Set} →
        ((x : A) → C (inj₁ x)) → ((x : B) → C (inj₂ x)) →
        ((x : A ⊎ B) → C x)
[ f , g ] (inj₁ x) = f x
[ f , g ] (inj₂ y) = g y

[_,_]₁ : ∀ {A : Set} {B : Set} {C : A ⊎ B → Set₁} →
        ((x : A) → C (inj₁ x)) → ((x : B) → C (inj₂ x)) →
        ((x : A ⊎ B) → C x)
[ f , g ]₁ (inj₁ x) = f x
[ f , g ]₁ (inj₂ y) = g y

record Σ (X : Set) (Y : X → Set) : Set where
  constructor _,_
  field
    proj₁ : X
    proj₂ : Y proj₁

open Σ public

_×_ : Set → Set → Set
X × Y = Σ X λ _ → Y

data _≡_ {X : Set} (x : X) : X → Set where
  refl : x ≡ x

subst : ∀ {A} (P : A → Set) {x y} → x ≡ y → P x → P y
subst P refl p = p

Pow : Set → Set₁
Pow X = X → Set

_∈_ : ∀ {X} → X → Pow X → Set
x ∈ P = P x

infix 4 _⊆_
_⊆_ : ∀ {X} → Pow X → Pow X → Set
P ⊆ Q = ∀ {x} → x ∈ P → x ∈ Q

_∪_ : ∀ {X} → Pow X → Pow X → Pow X
P ∪ Q = λ x → P x ⊎ Q x

_⇒_ : ∀ {X} → Pow X → Pow X → Pow X
P ⇒ Q = λ x → x ∈ P → x ∈ Q

record _▷_ (I O : Set) : Set₁ where
  constructor _◃_/_
  field
    Parameter  : (o : O) → Set
    Arity      : ∀ {o} (p : Parameter o) → Set
    input      : ∀ {o} (p : Parameter o) (a : Arity p) → I

open _▷_ public

Sig = λ I → I ▷ I

⟦_⟧ : ∀ {I O} → I ▷ O → (Pow I → Pow O)
⟦ P ◃ A / s ⟧ X o = Σ (P o) λ p → ((a : A p) → X (s p a))

data μ {I} (Ω : Sig I) : Pow I where
  sup : ⟦ Ω ⟧ (μ Ω) ⊆ μ Ω

const^C : ∀ {I O} → Pow O → I ▷ O
const^C X = X ◃ (λ _ → ⊥) / λ x ()

_⊎^C_ : ∀ {I O} → I ▷ O → I ▷ O → I ▷ O
(P₁ ◃ A₁ / s₁) ⊎^C (P₂ ◃ A₂ / s₂) = (P₁ ∪ P₂) ◃ [ A₁ , A₂ ]₁ / [ s₁ , s₂ ]

_⊙^C_ : ∀ {I J} → I ▷ I → J ▷ J → (I × J) ▷ (I × J)
(P₁ ◃ A₁ / s₁) ⊙^C (P₂ ◃ A₂ / s₂) = (λ { (i , j) → P₁ i ⊎ P₂ j })
  ◃ [ A₁ , A₂ ]₁
  / (λ  { {_ , j} (inj₁ p₁) a₁ → s₁ p₁ a₁ , j
        ; {i , _} (inj₂ p₂) a₂ → i , s₂ p₂ a₂
        })

_⋆^C_ : ∀ {O} → O ▷ O → Pow O → O ▷ O
Σ ⋆^C X = const^C X ⊎^C Σ

_⋆_ : ∀ {O} → O ▷ O → Pow O → Pow O
Σ ⋆ X = μ (Σ ⋆^C X)

Alg : ∀ {I} → Sig I → Pow I → Set
Alg Ω X = ⟦ Ω ⟧ X ⊆ X

act : ∀ {O} {Σ : O ▷ O} {X} → Alg Σ (Σ ⋆ X)
act (p , k) = sup (inj₂ p , k)

Hom : ∀ {I J} → Sig (I × J) → Pow (I × J) → Pow I → Sig J → Pow J → Set
Hom Ω U V Ψ W = Alg  (const^C U ⊎^C Ω)
                     ((V ∘ proj₁) ⇒ ((Ψ ⋆ W) ∘ proj₂))

_⋊_ : ∀ {I O} (C : I ▷ O) Z → (I × Z) ▷ (O × Z)
(P ◃ A / s) ⋊ Z = (P ∘ proj₁) ◃ A / λ {oz} p a → s p a , proj₂ oz

record ContainerMorphism
    {I₁ I₂ O₁ O₂}
    (C₁ : I₁ ▷ O₁) (C₂ : I₂ ▷ O₂)
    (f : I₁ → I₂) (g : O₁ → O₂)
    (_∼_ : I₂ → I₂ → Set) (_≈_ : Set → Set → Set)
    (_·_ : ∀ {A B} → A ≈ B → A → B) : Set where
  field
    parameter  : Parameter C₁ ⊆ Parameter C₂ ∘ g
    arity      : ∀ {o} {p₁ : Parameter C₁ o} →
                 Arity C₂ (parameter p₁) ≈ Arity C₁ p₁
    coherent   : ∀ {o} {p₁ : Parameter C₁ o} {a₂ : Arity C₂ (parameter p₁)} →
                 f (input C₁ p₁ (arity · a₂)) ∼ input C₂ (parameter p₁) a₂

open ContainerMorphism public

_⇛[_/_]_ : ∀ {I₁ I₂ O₁ O₂} → I₁ ▷ O₁ → (I₁ → I₂) → (O₁ → O₂) →
           I₂ ▷ O₂ → Set
C₁ ⇛[ f / g ] C₂ = ContainerMorphism C₁ C₂ f g _≡_  (λ R₂ R₁ → R₂ → R₁)
                                                    (λ f x → f x)

_⇛[_]_ : ∀ {I J} → I ▷ I → (I → J) → J ▷ J → Set
C₁ ⇛[ f ] C₂ = C₁ ⇛[ f / f ] C₂

⟪_⟫ : ∀ {I J} {C₁ : I ▷ I} {C₂ : J ▷ J} {f : I → J} →
      C₁ ⇛[ f ] C₂ → (X : Pow J) → ⟦ C₁ ⟧ (X ∘ f) ⊆ ⟦ C₂ ⟧ X ∘ f
⟪ m ⟫ X (c , k) = parameter m c , λ a₂ →
  subst X (coherent m) (k (arity m a₂))

------------------------------------------------------------------------

weaken : ∀ {I J} {Ω : Sig I} {Ψ : Sig J} {X : Pow J} {f : I → J} →
         Alg Ψ X → Ω ⇛[ f ] Ψ → Alg Ω (X ∘ f)
weaken {X = X} φ m (p , k) = φ (⟪ m ⟫ X (p , k))

lift : ∀ {I J} {Ω : Sig I} {U : Pow (I × J)} {V : Pow I} {Ψ : Sig J} {W : Pow J} →
       Hom (Ω ⋊ J)    U V Ψ W →
       Hom (Ω ⊙^C Ψ)  U V Ψ W
lift φ (inj₁ u , _)         = φ (inj₁ u , λ ())
lift φ (inj₂ (inj₁ p) , k)  = φ (inj₂ p , k)
lift φ (inj₂ (inj₂ p) , k)  = λ v → act (p , λ a → k a v)

handle : ∀ {I J K} {Ω : Sig I} {Ω′ : Sig J} {Ω″ : Sig K}
         {U : Pow (J × K)} {V : Pow J} {W : Pow K} {f : I → J × K} →
         Hom (Ω′ ⋊ K) U V Ω″ W → Ω ⇛[ f ] (Ω′ ⊙^C Ω″) →
         ∀ {i} → i ∈ (Ω ⋆ (U ∘ f)) → let (j , k) = f i in
         j ∈ V → k ∈ (Ω″ ⋆ W)
handle φ m (sup (inj₁ u  , _))  v = φ (inj₁ u , λ ()) v
handle φ m (sup (inj₂ p  , k))  v = weaken {!lift φ!} {!!} {!!}

-- Expected outcome:
-- giving "lift φ" twice should give the same error twice.
