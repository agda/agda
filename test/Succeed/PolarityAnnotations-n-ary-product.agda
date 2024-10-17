{-# OPTIONS --polarity #-}

open import Agda.Builtin.Nat

record _×_ (@++ A B : Set) : Set where
  field fst : A
        snd : B

n-ary : Nat → Set₁
n-ary 0 = @++ Set → Set
n-ary (suc n) = @++ Set → n-ary n

Product' : @++ (@++ Set → Set) → ∀ n → n-ary n
Product' S zero = S
Product' S (suc n) A = Product' (λ X → S (A × X)) n

Product : ∀ n → n-ary n
Product = Product' λ X → X

n-app : ∀ n (@++ X : Set) → @++ n-ary n → Set
n-app zero X F = F X
n-app (suc n) X F = n-app n X (F X)

data D : Set where
  node : (n : Nat) → n-app n D (Product n) → D
