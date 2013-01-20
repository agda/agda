module Issue784.Context where

open import Data.List using (List; []; _∷_; _++_; [_]; filter) renaming (map to mapL)
import Level

open import Issue784.Values

record Context ℓ : Set (Level.suc ℓ) where
  constructor context
  field get : Values ℓ

signature : ∀ {ℓ} → Context ℓ → Types ℓ
signature = types ∘ Context.get

ctxnames : ∀ {ℓ} → Context ℓ → Names
ctxnames = names ∘ Context.get

NonRepetitiveContext : ∀ {ℓ} → Context ℓ → _
NonRepetitiveContext = NonRepetitiveNames ∘ Context.get

getBySignature : ∀ {ℓ} {n : String} {A : Set ℓ} {x : Context ℓ} → (n , A) ∈ signature x → A
getBySignature {x = x} = getBySignature′ {x = Context.get x} where
  getBySignature′ : ∀ {ℓ} {n : String} {A : Set ℓ} {x : Values ℓ} → (n , A) ∈ types x → A
  getBySignature′ {x = []} ()
  getBySignature′ {x = (_ , _ , à) ∷ _} (here {x = ._} {xs = ._} p) = ≡-elim′ proj₂ (≡-sym p) à
  getBySignature′ {x = _ ∷ _} (there {x = ._} {xs = ._} p) = getBySignature′ p
