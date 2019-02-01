module Issue840a where

------------------------------------------------------------------------
-- Prelude

record ⊤ : Set where

data ⊥ : Set where

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

data Bool : Set where
  true false : Bool

{-# BUILTIN BOOL  Bool  #-}
{-# BUILTIN TRUE  true  #-}
{-# BUILTIN FALSE false #-}

postulate String : Set

{-# BUILTIN STRING String #-}

primitive primStringEquality : String → String → Bool

infixr 4 _,_

record Σ (A : Set) (B : A → Set) : Set where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B proj₁

------------------------------------------------------------------------
-- Other stuff

mutual

  infixl 5 _,_∶_

  data Signature : Set₁ where
    ∅     : Signature
    _,_∶_ : (Sig : Signature)
            (ℓ : String)
            (A : Record Sig → Set) →
            Signature

  record Record (Sig : Signature) : Set where
    eta-equality
    inductive
    constructor rec
    field fun : Record-fun Sig

  Record-fun : Signature → Set
  Record-fun ∅             = ⊤
  Record-fun (Sig , ℓ ∶ A) = Σ (Record Sig) A

_∈_ : String → Signature → Set
ℓ ∈ ∅              = ⊥
ℓ ∈ (Sig , ℓ′ ∶ A) with primStringEquality ℓ ℓ′
... | true  = ⊤
... | false = ℓ ∈ Sig

Restrict : (Sig : Signature) (ℓ : String) → ℓ ∈ Sig → Signature
Restrict ∅              ℓ ()
Restrict (Sig , ℓ′ ∶ A) ℓ ℓ∈ with primStringEquality ℓ ℓ′
... | true  = Sig
... | false = Restrict Sig ℓ ℓ∈

Proj : (Sig : Signature) (ℓ : String) {ℓ∈ : ℓ ∈ Sig} →
       Record (Restrict Sig ℓ ℓ∈) → Set
Proj ∅              ℓ {}
Proj (Sig , ℓ′ ∶ A) ℓ {ℓ∈} with primStringEquality ℓ ℓ′
... | true  = A
... | false = Proj Sig ℓ {ℓ∈}

_∣_ : {Sig : Signature} → Record Sig →
      (ℓ : String) {ℓ∈ : ℓ ∈ Sig} → Record (Restrict Sig ℓ ℓ∈)
_∣_ {Sig = ∅}            r       ℓ {}
_∣_ {Sig = Sig , ℓ′ ∶ A} (rec r) ℓ {ℓ∈} with primStringEquality ℓ ℓ′
... | true  = Σ.proj₁ r
... | false = _∣_ (Σ.proj₁ r) ℓ {ℓ∈}

infixl 5 _·_

_·_ : {Sig : Signature} (r : Record Sig)
      (ℓ : String) {ℓ∈ : ℓ ∈ Sig} →
      Proj Sig ℓ {ℓ∈} (r ∣ ℓ)
_·_ {Sig = ∅}            r       ℓ {}
_·_ {Sig = Sig , ℓ′ ∶ A} (rec r) ℓ {ℓ∈} with primStringEquality ℓ ℓ′
... | true  = Σ.proj₂ r
... | false = _·_ (Σ.proj₁ r) ℓ {ℓ∈}

R : Set → Signature
R A = ∅ , "f"     ∶ (λ _ → A → A)
        , "x"     ∶ (λ _ → A)
        , "lemma" ∶ (λ r → ∀ y → (r · "f") y ≡ y)

record GS (A B : Set) : Set where
  field
    get     : A → B
    set     : A → B → A
    get-set : ∀ a b → get (set a b) ≡ b
    set-get : ∀ a → set a (get a) ≡ a

f : {A : Set} →
    GS (Record (R A))
       (Record (∅ , "f"     ∶ (λ _ → A → A)
                  , "lemma" ∶ (λ r → ∀ x → (r · "f") x ≡ x)))
f = record
  { set     = λ r f-lemma → rec (rec (rec (rec _
                , f-lemma · "f")
                , r · "x")
                , f-lemma · "lemma")
  ; get-set = λ { (rec (rec (rec (_ , _) , _) , _))
                  (rec (rec (_ , _) , _)) → refl }
  ; set-get = λ { (rec (rec (rec (rec _ , _) , _) , _)) → refl }
  }
