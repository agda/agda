module Issue784.RefAPI where

open import Issue784.Values public
open import Issue784.Context -- that should be private
open import Issue784.Transformer public

open import Data.List public using (List; []; _∷_; [_])
open import Data.Nat
open import Relation.Binary.PropositionalEquality.TrustMe

private
  postulate
    _seq_ : ∀ {a b} {A : Set a} {B : Set b} → A → B → B

    nativeRef : (A : Set) → Set
    -- create new reference and initialize it with passed value
    nativeNew-ℕ : ℕ → nativeRef ℕ
    -- increment value in place
    nativeInc-ℕ : nativeRef ℕ → Unit
    nativeGet-ℕ : nativeRef ℕ → ℕ
    nativeFree-ℕ : nativeRef ℕ → Unit

data Exact {ℓ} {A : Set ℓ} : A → Set ℓ where
  exact : ∀ a → Exact a

getExact : ∀ {ℓ} {A : Set ℓ} {a : A} → Exact a → A
getExact (exact a) = a

≡-exact : ∀ {ℓ} {A : Set ℓ} {a : A} (e : Exact a) → getExact e ≡ a
≡-exact (exact a) = refl

Ref-ℕ : ℕ → Set
Ref-ℕ a = Σ[ native ∈ nativeRef ℕ ] nativeGet-ℕ native ≡ a

private
  -- making these private to avoid further using
  -- which may lead to inconsistency
  proofNew-ℕ : ∀ a → Ref-ℕ a
  proofNew-ℕ a = nativeNew-ℕ a , trustMe

  proofInc-ℕ : ∀ {a} → Ref-ℕ a → Ref-ℕ (suc a)
  proofInc-ℕ (r , _) = (nativeInc-ℕ r) seq (r , trustMe)

  proofGet-ℕ : ∀ {a} → Ref-ℕ a → Exact a
  proofGet-ℕ (r , p) = ≡-elim′ Exact p (exact $ nativeGet-ℕ r)

  proofFree-ℕ : {a : ℕ} → Ref-ℕ a → Unit
  proofFree-ℕ (r , _) = nativeFree-ℕ r

new-ℕ : ∀ a n → Transformer! [] [(n , Unique (Ref-ℕ a))]
new-ℕ a n ctx nr-v []⊆v nr-v∪n = context w , (≡⇒≋ $ ≡-trans p₁ p₂) where
    v = Context.get ctx
    w = v ∪ [(n , Unique (Ref-ℕ a) , unique (proofNew-ℕ a))]
    p₁ : types (v ∪ [(n , Unique (Ref-ℕ a) , _)]) ≡ types v ∪ [(n , Unique (Ref-ℕ a))]
    p₁ = t-x∪y v [(n , Unique (Ref-ℕ a) , _)]
    p₂ : types v ∪ [(n , Unique (Ref-ℕ a))] ≡ types v ∖∖ [] ∪ [(n , Unique (Ref-ℕ a))]
    p₂ = ≡-cong (λ x → x ∪ [(n , Unique (Ref-ℕ a))]) (≡-sym $ t∖[]≡t $ types v)

inc-ℕ : ∀ {a} n → Transformer! [(n , Unique (Ref-ℕ a))] [(n , Unique (Ref-ℕ (suc a)))]
inc-ℕ {a} n ctx nr-v n⊆v nr-v∪n = context w , (≡⇒≋ $ ≡-trans p₁ p₂) where
    v = Context.get ctx
    r = unique ∘ proofInc-ℕ ∘ Unique.get ∘ getBySignature ∘ n⊆v $ here refl
    w = v ∖∖ [ n ] ∪ [(n , Unique (Ref-ℕ $ suc a) , r)]
    p₁ : types (v ∖∖ [ n ] ∪ [(n , Unique (Ref-ℕ $ suc a) , r)]) ≡ types (v ∖∖ [ n ]) ∪ [(n , Unique (Ref-ℕ $ suc _))]
    p₁ = t-x∪y (v ∖∖ [ n ]) _
    p₂ : types (v ∖∖ [ n ]) ∪ [(n , Unique (Ref-ℕ $ suc a))] ≡ types v ∖∖ [ n ] ∪ [(n , Unique (Ref-ℕ $ suc _))]
    p₂ = ≡-cong (λ x → x ∪ [(n , Unique (Ref-ℕ $ suc a))]) (t-x∖y v [ n ])

get-ℕ : (r n : String) {r≢!n : r s-≢! n} {a : ℕ} →
    Transformer ([(r , Unique (Ref-ℕ a))] , nr-[a]) ((r , Unique (Ref-ℕ a)) ∷ [(n , Pure (Exact a))] , (x≢y⇒x∉l⇒x∉y∷l (s-≢!⇒≢? r≢!n) λ()) ∷ nr-[a])
get-ℕ r n {a = a} ctx nr-v h⊆v _ = context w , ≋-trans p₁ (≋-trans p₂ p₃) where
    v = Context.get ctx
    pr : Pure (Exact a)
    pr = pure ∘ proofGet-ℕ ∘ Unique.get ∘ getBySignature ∘ h⊆v $ here refl
    w = v ∪ [(n , Pure (Exact a) , pr)]
    p₁ : types (v ∪ [(n , Pure (Exact a) , pr)]) ≋ types v ∪ [(n , Pure (Exact a))]
    p₁ = ≡⇒≋ $ t-x∪y v [(n , Pure (Exact a) , pr)]
    p₂ : types v ∪ [(n , Pure (Exact a))] ≋ (types v ∖∖ [ r ] ∪ [(r , Unique (Ref-ℕ _))]) ∪ [(n , Pure (Exact a))]
    p₂ = x≋x̀⇒x∪y≋x̀∪y (≋-trans g₁ g₂) [(n , Pure (Exact a))] where
        g₁ : types v ≋ [(r , Unique (Ref-ℕ _))] ∪ types v ∖∖ [ r ]
        g₁ = t₁⊆t₂⇒t₂≋t₁∪t₂∖nt₁ nr-[a] (nr-x⇒nr-t-x nr-v) h⊆v
        g₂ : [(r , Unique (Ref-ℕ _))] ∪ types v ∖∖ [ r ] ≋ types v ∖∖ [ r ] ∪ [(r , Unique (Ref-ℕ _))]
        g₂ = ∪-sym [(r , Unique (Ref-ℕ _))] (types v ∖∖ [ r ])
    p₃ : (types v ∖∖ [ r ] ∪ [(r , Unique (Ref-ℕ a))]) ∪ [(n , Pure (Exact a))] ≋ types v ∖∖ [ r ] ∪ ((r , Unique (Ref-ℕ _)) ∷ [(n , Pure (Exact a))])
    p₃ = ≡⇒≋ $ ∪-assoc (types v ∖∖ [ r ]) [(r , Unique (Ref-ℕ _))] [(n , Pure (Exact a))]

free-ℕ : (h : String) {a : ℕ} → Transformer! [(h , Unique (Ref-ℕ a))] []
free-ℕ h ctx nr-v h⊆v _ = u seq (context w , ≡⇒≋ p) where
    v = Context.get ctx
    u = proofFree-ℕ ∘ Unique.get ∘ getBySignature ∘ h⊆v $ here refl
    w = v ∖∖ [ h ]
    p : types (v ∖∖ [ h ]) ≡ types v ∖∖ [ h ] ∪ []
    p = ≡-trans (t-x∖y v [ h ]) (≡-sym $ x∪[]≡x (types v ∖∖ [ h ]))
