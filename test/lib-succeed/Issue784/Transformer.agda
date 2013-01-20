module Issue784.Transformer where

open import Data.List using (List; []; _∷_; _++_; [_]; filter) renaming (map to mapL)
import Level

open import Issue784.Values
open import Issue784.Context

Transformer : ∀ {ℓ} → NonRepetitiveTypes ℓ → NonRepetitiveTypes ℓ → Set (Level.suc ℓ)
Transformer {ℓ} (t-in , nr-in) (t-out , nr-out) =
  (v : Context ℓ) → NonRepetitiveContext v → t-in ⊆ signature v → NonRepetitive (ctxnames v ∖ names t-in ∪ names t-out) →
  Σ[ w ∶ Context ℓ ] signature w ≋ signature v ∖∖ names t-in ∪ t-out

pipe : ∀ {ℓ} {t-in₁ t-out₁ t-in₂ t-out₂ : Types ℓ} {nr-in₁ nr-out₁ nr-in₂ nr-out₂} →
       Transformer (t-in₁ , nr-in₁) (t-out₁ , nr-out₁) →
       Transformer (t-in₂ , nr-in₂) (t-out₂ , nr-out₂) →
       let n-out₁ = names t-out₁
           n-in₂ = names t-in₂
           t-in = t-in₁ ∪ (t-in₂ ∖∖ n-out₁)
           t-out = t-out₁ ∖∖ n-in₂ ∪ t-out₂
       in
       filter-∈ t-out₁ n-in₂ ≋ filter-∈ t-in₂ n-out₁ →
       (nr-in : NonRepetitiveNames t-in) (nr-out : NonRepetitiveNames t-out) →
       Transformer (t-in , nr-in) (t-out , nr-out)
pipe {ℓ} {t-in₁} {t-out₁} {t-in₂} {t-out₂} {nr-in₁} {nr-out₁} {nr-in₂} {nr-out₂} tr₁ tr₂ pr-t nr-in nr-out = tr where
    n-in₁ = names t-in₁
    n-out₁ = names t-out₁
    n-in₂ = names t-in₂
    n-out₂ = names t-out₂

    t-in = t-in₁ ∪ (t-in₂ ∖∖ n-out₁)
    t-out = (t-out₁ ∖∖ n-in₂) ∪ t-out₂

    tr : Transformer (t-in , nr-in) (t-out , nr-out)
    tr ctx nr-v t-ì⊆v nr-ò = context w , w≋out where
        v = Context.get ctx
        n-in = names t-in
        v̀ = filter-∈ v n-in
        nr-v̀ : NonRepetitiveNames v̀
        nr-v̀ = nr-x⇒nr-x∩y nr-v n-in

        v̀≋i : types v̀ ≋ t-in
        v̀≋i = ≋-sym $ ≋-trans p₁ p₂ where
            p₁ : t-in ≋ filter-∈ (types v) n-in
            p₁ = t₁⊆t₂⇒t₁≋f∈-t₂-nt₁ nr-in (≡-elim′ NonRepetitive (≡-sym $ n-types v) nr-v) t-ì⊆v
            p₂ : filter-∈ (types v) n-in ≋ types v̀
            p₂ = ≡⇒≋ $ ≡-sym $ t-filter-∈ v n-in

        -- transformer₁
        i₁⊆v̀ : t-in₁ ⊆ types v̀
        i₁⊆v̀ = x⊆y≋z (x⊆x∪y t-in₁ (t-in₂ ∖∖ n-out₁)) (≋-sym v̀≋i)

        v̀∖i₁∪o₁≋i₂∖o₁∪o₁ : types v̀ ∖∖ n-in₁ ∪ t-out₁ ≋ t-in₂ ∖∖ n-out₁ ∪ t-out₁
        v̀∖i₁∪o₁≋i₂∖o₁∪o₁ = x≋x̀⇒x∪y≋x̀∪y p₂ t-out₁ where
            p₁ : NonRepetitiveNames (types v̀)
            p₁ = nr-x≋y (≡⇒≋ $ ≡-sym $ n-types v̀) nr-v̀
            p₂ : types v̀ ∖∖ n-in₁ ≋ t-in₂ ∖∖ n-out₁
            p₂ = t≋t₁∪t₂⇒t∖t₁≋t₂ p₁ t-in₁ (t-in₂ ∖∖ n-out₁) v̀≋i

        n-v̀∖i₁∪o₁≋i₂∖o₁∪o₁ : names v̀ ∖ n-in₁ ∪ n-out₁ ≋ n-in₂ ∖ n-out₁ ∪ n-out₁
        n-v̀∖i₁∪o₁≋i₂∖o₁∪o₁ = x≋x̀⇒x∪y≋x̀∪y p₃ n-out₁ where
            p₁ : names v̀ ≋ n-in
            p₁ = ≋-trans (≡⇒≋ $ n-filter-∈ v n-in) (y⊆x⇒x∩y≋y nr-in nr-v (≡-elim′ (λ x → n-in ⊆ x) (n-types v) (x⊆y⇒nx⊆ny t-ì⊆v)))
            p₂ : n-in ≋ n-in₁ ∪ (n-in₂ ∖ n-out₁)
            p₂ = ≡⇒≋ $ ≡-trans (n-x∪y t-in₁ $ t-in₂ ∖∖ n-out₁) (≡-cong (λ x → n-in₁ ∪ x) (n-x∖y t-in₂ n-out₁))
            p₃ : names v̀ ∖ n-in₁ ≋ n-in₂ ∖ n-out₁
            p₃ = x≋y∪z⇒x∖y≋z (nr-x≋y (≋-sym p₁) nr-in) n-in₁ (n-in₂ ∖ n-out₁) (≋-trans p₁ p₂)

        nr-v̀∖i₁∪o₁ : NonRepetitive (names v̀ ∖ n-in₁ ∪ n-out₁)
        nr-v̀∖i₁∪o₁ = nr-x≋y (≋-sym n-v̀∖i₁∪o₁≋i₂∖o₁∪o₁) p₁ where
            p₁ : NonRepetitive (n-in₂ ∖ n-out₁ ∪ n-out₁)
            p₁ = nr-x∖y∪y nr-in₂ nr-out₁

        w-all₁ : Σ[ w ∶ Context ℓ ] signature w ≋ signature (context v̀) ∖∖ names t-in₁ ∪ t-out₁
        w-all₁ = tr₁ (context v̀) nr-v̀ i₁⊆v̀ nr-v̀∖i₁∪o₁

        w₁ = Context.get $ proj₁ w-all₁
        w₁≋v̀∖i₁∪o₁ = proj₂ w-all₁

        -- transformer₂
        n-w₁≋v̀∖i₁∪o₁ : names w₁ ≋ names v̀ ∖ names t-in₁ ∪ names t-out₁
        n-w₁≋v̀∖i₁∪o₁ = ≡-elim p₆ p₅ where
            p₁ : names (types w₁) ≋ names (types v̀ ∖∖ names t-in₁ ∪ t-out₁)
            p₁ = n-x≋y w₁≋v̀∖i₁∪o₁
            p₂ : names (types v̀ ∖∖ names t-in₁ ∪ t-out₁) ≡ names (types v̀ ∖∖ names t-in₁) ∪ names t-out₁
            p₂ = n-x∪y (types v̀ ∖∖ names t-in₁) t-out₁
            p₃ : names (types v̀ ∖∖ names t-in₁) ≡ names (types v̀) ∖ names t-in₁
            p₃ = n-x∖y (types v̀) (names t-in₁)
            p₄ : names (types w₁) ≋ names (types v̀ ∖∖ names t-in₁) ∪ names t-out₁
            p₄ = ≡-elim′ (λ x → names (types w₁) ≋ x) p₂ p₁
            p₅ : names (types w₁) ≋ names (types v̀) ∖ names t-in₁ ∪ names t-out₁
            p₅ = ≡-elim′ (λ x → names (types w₁) ≋ x ∪ names t-out₁) p₃ p₄
            p₆ : (names (types w₁) ≋ names (types v̀) ∖ names t-in₁ ∪ names t-out₁) ≡
                 (names w₁ ≋ names v̀ ∖ names t-in₁ ∪ names t-out₁)
            p₆ = ≡-cong₂ (λ x y → x ≋ y ∖ names t-in₁ ∪ names t-out₁) (n-types w₁) (n-types v̀)

        nr-w₁ : NonRepetitiveNames w₁
        nr-w₁ = nr-x≋y (≋-sym n-w₁≋v̀∖i₁∪o₁) nr-v̀∖i₁∪o₁

        i₂⊆w₁ : t-in₂ ⊆ types w₁
        i₂⊆w₁ = x⊆y≋z (x≋y⊆z (≋-sym p₁) p₄) (≋-sym w₁≋v̀∖i₁∪o₁) where
            p₁ : t-in₂ ≋ (t-in₂ ∖∖ n-out₁) ∪ filter-∈ t-in₂ n-out₁
            p₁ = t≋t∖n∪t∩n t-in₂ n-out₁
            p₂ : filter-∈ t-in₂ n-out₁ ⊆ t-out₁
            p₂ = x≋y⊆z pr-t $ x∩y⊆x t-out₁ n-in₂
            p₃ : types v̀ ∖∖ n-in₁ ≋ t-in₂ ∖∖ n-out₁
            p₃ = t≋t₁∪t₂⇒t∖t₁≋t₂ (≡-elim′ NonRepetitive (≡-sym $ n-types v̀) nr-v̀) t-in₁ (t-in₂ ∖∖ n-out₁) v̀≋i
            p₄ : (t-in₂ ∖∖ n-out₁) ∪ (filter-∈ t-in₂ n-out₁) ⊆ (types v̀ ∖∖ n-in₁) ∪ t-out₁
            p₄ = x∪y⊆x̀∪ỳ (≋⇒⊆ $ ≋-sym p₃) p₂

        w₁∖i₂∪o₂≋out : types w₁ ∖∖ n-in₂ ∪ t-out₂ ≋ t-out
        w₁∖i₂∪o₂≋out = x≋x̀⇒x∪y≋x̀∪y p₄ t-out₂ where
            p₁ : t-in₂ ∖∖ n-out₁ ∪ t-out₁ ≋ t-out₁ ∖∖ n-in₂ ∪ t-in₂
            p₁ = ≋-sym $ x∖y∪y≋y∖x∪x t-out₁ t-in₂ pr-t
            p₂ : (t-out₁ ∖∖ n-in₂) ∪ t-in₂ ≋ t-in₂ ∪ (t-out₁ ∖∖ n-in₂)
            p₂ = ∪-sym (t-out₁ ∖∖ n-in₂) t-in₂
            p₃ : types w₁ ≋ t-in₂ ∪ (t-out₁ ∖∖ n-in₂)
            p₃ = ≋-trans w₁≋v̀∖i₁∪o₁ $ ≋-trans v̀∖i₁∪o₁≋i₂∖o₁∪o₁ $ ≋-trans p₁ p₂
            p₄ : types w₁ ∖∖ n-in₂ ≋ t-out₁ ∖∖ n-in₂
            p₄ = t≋t₁∪t₂⇒t∖t₁≋t₂ (nr-x≋y (≡⇒≋ $ ≡-sym $ n-types w₁) nr-w₁) t-in₂ (t-out₁ ∖∖ n-in₂) p₃

        nr-w₁∖i₂∪o₂ : NonRepetitive (names w₁ ∖ n-in₂ ∪ n-out₂)
        nr-w₁∖i₂∪o₂ = ≡-elim′ NonRepetitive p₄ p₅ where
            p₁ : names (types w₁ ∖∖ n-in₂ ∪ t-out₂) ≡ names (types w₁ ∖∖ n-in₂) ∪ n-out₂
            p₁ = n-x∪y (types w₁ ∖∖ n-in₂) t-out₂
            p₂ : names (types w₁ ∖∖ n-in₂) ∪ n-out₂ ≡ (names (types w₁) ∖ n-in₂) ∪ n-out₂
            p₂ = ≡-cong (λ x → x ∪ names t-out₂) (n-x∖y (types w₁) n-in₂)
            p₃ : (names (types w₁) ∖ n-in₂) ∪ n-out₂ ≡ names w₁ ∖ n-in₂ ∪ n-out₂
            p₃ = ≡-cong (λ x → x ∖ n-in₂ ∪ n-out₂) (n-types w₁)
            p₄ : names (types w₁ ∖∖ n-in₂ ∪ t-out₂) ≡ names w₁ ∖ n-in₂ ∪ n-out₂
            p₄ = ≡-trans p₁ $ ≡-trans p₂ p₃
            p₅ : NonRepetitiveNames (types w₁ ∖∖ n-in₂ ∪ t-out₂)
            p₅ = nr-x≋y (≋-sym $ n-x≋y w₁∖i₂∪o₂≋out) nr-out

        w-all₂ : Σ[ w ∶ Context ℓ ] signature w ≋ signature (context w₁) ∖∖ names t-in₂ ∪ t-out₂
        w-all₂ = tr₂ (context w₁) nr-w₁ i₂⊆w₁ nr-w₁∖i₂∪o₂

        w₂ = Context.get $ proj₁ w-all₂
        w₂≋out : types w₂ ≋ t-out
        w₂≋out = ≋-trans (proj₂ w-all₂) w₁∖i₂∪o₂≋out

        w = v ∖∖ n-in ∪ w₂ ∶ Values ℓ
        w≋out : types w ≋ types v ∖∖ n-in ∪ t-out
        w≋out = ≋-trans (≡⇒≋ p₁) p₂ where
            p₁ : types (v ∖∖ n-in ∪ w₂) ≡ types v ∖∖ n-in ∪ types w₂
            p₁ = ≡-trans (t-x∪y (v ∖∖ n-in) w₂) (≡-cong (λ x → x ∪ types w₂) (t-x∖y v n-in))
            p₂ : types v ∖∖ n-in ∪ types w₂ ≋ types v ∖∖ n-in ∪ t-out
            p₂ = y≋ỳ⇒x∪y≋x∪ỳ (types v ∖∖ n-in) w₂≋out

Transformer! : ∀ {ℓ} (t-in : Types ℓ) (t-out : Types ℓ) {nr!-in : NonRepetitiveNames! t-in} {nr!-out : NonRepetitiveNames! t-out} → Set (Level.suc ℓ)
Transformer! t-in t-out {nr!-in = nr!-in} {nr!-out} = Transformer (t-in , s-nr!⇒nr nr!-in) (t-out , s-nr!⇒nr nr!-out)

infix 1 _:=_
_:=_ : ∀ {ℓ} {A : String → Set ℓ} (n : String) → ((n : String) → A n) → A n
n := f = f n

infixl 0 _⇒⟦_⟧⇒_
_⇒⟦_⟧⇒_ : ∀ {ℓ} {t-in₁ t-out₁ t-in₂ t-out₂ : Types ℓ}
          {nr!-in₁ : NonRepetitiveNames! t-in₁}
          {nr!-out₁ : NonRepetitiveNames! t-out₁}
          {nr!-in₂ : NonRepetitiveNames! t-in₂}
          {nr!-out₂ : NonRepetitiveNames! t-out₂} →
       Transformer (t-in₁ , s-nr!⇒nr nr!-in₁) (t-out₁ , s-nr!⇒nr nr!-out₁) →

       let n-out₁ = names t-out₁
           n-in₂ = names t-in₂
           t-in = t-in₁ ∪ (t-in₂ ∖∖ n-out₁)
           t-out = t-out₁ ∖∖ n-in₂ ∪ t-out₂
       in
       filter-∈ t-out₁ n-in₂ ≋ filter-∈ t-in₂ n-out₁ →
       {nr!-in : NonRepetitiveNames! t-in} →
       {nr!-out : NonRepetitiveNames! t-out} →

       Transformer (t-in₂ , s-nr!⇒nr nr!-in₂) (t-out₂ , s-nr!⇒nr nr!-out₂) →
       Transformer (t-in , s-nr!⇒nr nr!-in) (t-out , s-nr!⇒nr nr!-out)

_⇒⟦_⟧⇒_ {nr!-in₁ = nr!-in₁} {nr!-out₁ = nr!-out₁} {nr!-in₂ = nr!-in₂} {nr!-out₂ = nr!-out₂}
        tr₁ f≋f {nr!-in = nr!-in} {nr!-out = nr!-out} tr₂ =
    pipe {nr-in₁ = s-nr!⇒nr nr!-in₁} {nr-out₁ = s-nr!⇒nr nr!-out₁} {nr-in₂ = s-nr!⇒nr nr!-in₂} {nr-out₂ = s-nr!⇒nr nr!-out₂}
        tr₁ tr₂ f≋f (s-nr!⇒nr nr!-in) (s-nr!⇒nr nr!-out)

record Pure {ℓ} (A : Set ℓ) : Set ℓ where
    constructor pure
    field get : A

record Unique {ℓ} (A : Set ℓ) : Set ℓ where
    constructor unique
    field get : A

extract : ∀ {ℓ} {n : String} {A : Set ℓ} → let t = [ (n , Pure A) ] in {nr!-t : NonRepetitiveNames! t} → Transformer ([] , []) (t , s-nr!⇒nr nr!-t) → A
extract {n = n} {A = A} {nr!-t = nr!-t} tr =
  let e = n , Pure A
      v , t-v≋t = (tr (context []) [] (≋⇒⊆ refl) (s-nr!⇒nr nr!-t) ∶ (Σ[ v ∶ Context _ ] signature v ≋ [ e ]))
   in Pure.get ∘ getBySignature $ a∈x⇒x≋y⇒a∈y (here refl ∶ e ∈ [ e ]) (≋-sym t-v≋t)
