module Issue846.DivModUtils where

open import Data.Nat
open import Data.Bool

open import Issue846.OldDivMod
open import Relation.Nullary
open import Data.Nat.Properties hiding (≤-antisym)
open import Data.Fin using (Fin; toℕ; zero; suc; fromℕ≤)
open import Data.Fin.Properties using ( bounded; toℕ-fromℕ≤; toℕ-injective )
open import Relation.Binary.PropositionalEquality
open import Function
open import Data.Product
open import Relation.Binary hiding (NonEmpty)
open import Data.Empty
open import Relation.Nullary.Negation
open ≡-Reasoning
open ≤-Reasoning
  renaming (begin_ to start_; _∎ to _□; _≡⟨_⟩_ to _≡⟨_⟩'_)
open DecTotalOrder ≤-decTotalOrder using () renaming (refl to ≤-refl; antisym to ≤-antisym)


i+[j∸m]≡i+j∸m : ∀ i j m → m ≤ j → i + (j ∸ m) ≡ i + j ∸ m
i+[j∸m]≡i+j∸m i zero zero lt = refl
i+[j∸m]≡i+j∸m i zero (suc m) ()
i+[j∸m]≡i+j∸m i (suc j) zero lt = refl
i+[j∸m]≡i+j∸m i (suc j) (suc m) (s≤s m≤j) = begin
  i + (j ∸ m)             ≡⟨ i+[j∸m]≡i+j∸m i j m m≤j ⟩
  suc (i + j) ∸ suc m   ≡⟨ cong (λ y → y ∸ suc m) $ solve 2 (λ i' j' → con 1 :+ (i' :+ j') := i' :+ (con 1 :+ j')) refl i j ⟩
  (i + suc j) ∸ suc m ∎
  where
    open SemiringSolver

-- Following code taken from https://github.com/copumpkin/derpa/blob/master/REPA/Index.agda#L210

-- the next few bits are lemmas to prove uniqueness of euclidean division

-- first : for nonzero divisors, a nonzero quotient would require a larger
-- dividend than is consistent with a zero quotient, regardless of
-- remainders.

large : ∀ {d} {r : Fin (suc d)} x (r′ : Fin (suc d)) → toℕ r ≢ suc x * suc d + toℕ r′
large {d} {r} x r′ pf = irrefl pf (
    start
      suc (toℕ r)
    ≤⟨ bounded r ⟩
      suc d
    ≤⟨ m≤m+n (suc d) (x * suc d) ⟩
      suc d + x * suc d -- same as (suc x * suc d)
    ≤⟨ m≤m+n (suc x * suc d) (toℕ r′) ⟩
      suc x * suc d + toℕ r′ -- clearer in two steps, and we'd need assoc anyway
    □)
  where
  open ≤-Reasoning
  open Relation.Binary.StrictTotalOrder Data.Nat.Properties.strictTotalOrder

-- a raw statement of the uniqueness, in the arrangement of terms that's
-- easiest to work with computationally

addMul-lemma′ : ∀ x x′ d (r r′ : Fin (suc d)) → x * suc d + toℕ r ≡ x′ * suc d + toℕ r′ → r ≡ r′ × x ≡ x′
addMul-lemma′ zero zero d r r′ hyp = (toℕ-injective hyp) , refl
addMul-lemma′ zero (suc x′) d r r′ hyp = ⊥-elim (large x′ r′ hyp)
addMul-lemma′ (suc x) zero d r r′ hyp = ⊥-elim (large x r (sym hyp))
addMul-lemma′ (suc x) (suc x′) d r r′ hyp
                      rewrite +-assoc (suc d) (x * suc d) (toℕ r)
                            | +-assoc (suc d) (x′ * suc d) (toℕ r′)
                      with addMul-lemma′ x x′ d r r′ (cancel-+-left (suc d) hyp)
... | pf₁ , pf₂ = pf₁ , cong suc pf₂


-- and now rearranged to the order that Data.Nat.DivMod uses

addMul-lemma : ∀ x x′ d (r r′ : Fin (suc d)) → toℕ r + x * suc d ≡ toℕ r′ + x′ * suc d → r ≡ r′ × x ≡ x′
addMul-lemma x x′ d r r′ hyp rewrite +-comm (toℕ r) (x * suc d)
                                   | +-comm (toℕ r′) (x′ * suc d)
  = addMul-lemma′ x x′ d r r′ hyp


DivMod-lemma : ∀ x d (r : Fin (suc d)) → (res : DivMod (toℕ r + x * suc d) (suc d)) → res ≡ result x r refl
DivMod-lemma x d r (result q r′ eq) with addMul-lemma x q d r r′ eq
DivMod-lemma x d r (result .x .r eq) | refl , refl = cong (result x r) (proof-irrelevance eq refl) -- holy fuck


divMod-lemma : ∀ x d (r : Fin (suc d)) → (toℕ r + x * suc d) divMod suc d ≡ result x r refl
divMod-lemma x d r with (toℕ r + x * suc d) divMod suc d
divMod-lemma x d r | q rewrite DivMod-lemma x d r q = refl


-- End of copied code

mod-lemma : ∀ x d (r : Fin (suc d)) → (toℕ r + x * suc d) mod suc d ≡ r
mod-lemma x d r rewrite divMod-lemma x d r = refl


mod-suc : ∀ n
  →     n mod 7 ≡     zero
  → suc n mod 7 ≡ suc zero
mod-suc n eq with n divMod 7
mod-suc .(q * 7) refl | result q .zero refl = mod-lemma q 6 (suc zero)


mod-pred : ∀ n
  →  suc n mod 7 ≡ suc zero
  →      n mod 7 ≡     zero
mod-pred n eq with n divMod 7
mod-pred .(toℕ r + q * 7) eq | result q r refl with toℕ r ≤? 5
mod-pred .(toℕ r + q * 7) eq | result q r refl | yes p  = toℕ-injective eq4
  where r' = fromℕ≤ {suc (toℕ r)} {7} (s≤s (s≤s p))
        r'≡r = toℕ-fromℕ≤ (s≤s (s≤s p))
        eq4 = cong pred $ begin
          suc (toℕ r)
            ≡⟨ sym r'≡r ⟩
          toℕ r'
            ≡⟨ cong toℕ $ begin
              r'                        ≡⟨ sym (mod-lemma q 6 r') ⟩
              (toℕ r' + q * 7) mod 7    ≡⟨ cong (λ y → (y + q * 7) mod 7) r'≡r ⟩
              suc (toℕ r + q * 7) mod 7 ≡⟨ eq ⟩
              suc zero ∎ ⟩
          toℕ (suc (zero {7}))
            ≡⟨ refl ⟩
          suc zero ∎
mod-pred .(toℕ r + q * 7) eq | result q r refl | no ¬p with eq3
  where eq2 = begin
          6
            ≡⟨ ≤-antisym (≰⇒> ¬p) (pred-mono (bounded r)) ⟩
          toℕ r ∎
        eq3 = begin
          zero
            ≡⟨ sym (mod-lemma (suc q) 6 zero) ⟩
          (suc q * 7) mod 7
            ≡⟨ refl ⟩
          suc (6 + q * 7) mod 7
            ≡⟨ cong (λ y → suc (y + q * 7) mod 7) $ eq2 ⟩
          suc (toℕ r + q * 7) mod 7
            ≡⟨ eq ⟩
          suc zero ∎
... | ()

∸-mono₁ : ∀ i j k → i ≤ j →  i ∸ k ≤ j ∸ k
∸-mono₁ i j zero i≤j = i≤j
∸-mono₁ zero j (suc k) i≤j = z≤n
∸-mono₁ (suc i) zero (suc k) ()
∸-mono₁ (suc i) (suc j) (suc k) (s≤s i≤j) = ∸-mono₁ i j k i≤j

∸-mono₂ : ∀ i j k → j ≤ k → i ∸ j ≥ i ∸ k
∸-mono₂ i zero k j≤k = n∸m≤n k i
∸-mono₂ i (suc j) zero ()
∸-mono₂ zero (suc j) (suc k) j≤k = z≤n
∸-mono₂ (suc n) (suc j) (suc k) (s≤s j≤k) = ∸-mono₂ n j k j≤k

1' : Fin 7
1' = suc zero

lem-sub-p : ∀ n p → (suc n mod 7 ≡ 1') → 1 ≤ p → p ≤ 6 → ((suc n ∸ p) mod 7 ≢ 1')
lem-sub-p _ 0 _ () _ _
lem-sub-p n 1 eq1 _ _ eq2 with begin zero ≡⟨ sym (mod-pred n eq1) ⟩ n mod 7 ≡⟨ eq2 ⟩ suc zero ∎
... | ()
lem-sub-p n (suc (suc p)) eq _ ≤6 eq2 with n divMod 7 | mod-pred n eq
lem-sub-p .0 (suc (suc p)) _ _ ≤6 () | result zero .zero refl | refl
lem-sub-p .(7 + (q * 7)) (suc (suc p)) _ _ (s≤s (s≤s (≤4))) eq2 | result (suc q) .zero refl | refl = ⊥-elim $ 1+n≰n 1<1
  where <7 : (6 ∸ p) < 7
        <7 = s≤s (n∸m≤n p 6)
        eq4 = begin
            toℕ (fromℕ≤ <7) + q * 7
              ≡⟨ cong (λ y → y + q * 7) (toℕ-fromℕ≤ <7 )⟩
            (6 ∸ p) + q * 7
              ≡⟨ +-comm (6 ∸ p) (q * 7) ⟩
            q * 7 + (6 ∸ p)
              ≡⟨ i+[j∸m]≡i+j∸m (q * 7) 6 p (≤-steps 2 ≤4) ⟩
            (q * 7 + 6) ∸ p
              ≡⟨ cong (λ y → y ∸ p) (+-comm (q * 7) 6)⟩
            (6 + q * 7) ∸ p ∎
        eq5 = begin
            fromℕ≤ <7
              ≡⟨ sym (mod-lemma q 6 (fromℕ≤ <7)) ⟩
            (toℕ (fromℕ≤ <7) + q * 7) mod 7
              ≡⟨ cong (λ y → y mod 7) eq4 ⟩
            ((6 + q * 7) ∸ p) mod 7
              ≡⟨ eq2 ⟩
            suc zero ∎
        1<1 = start
            2                     ≤⟨ ∸-mono₂ 6 p 4 ≤4 ⟩
            6 ∸ p                 ≡⟨ sym (toℕ-fromℕ≤ <7) ⟩'
            toℕ (fromℕ≤ <7)       ≡⟨ cong toℕ eq5 ⟩'
            toℕ (suc (zero {7}))  ≡⟨ refl ⟩'
            suc zero □


-- bla = nonEmpty
