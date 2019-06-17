{-# OPTIONS --rewriting #-}


open import Agda.Builtin.Equality
{-# BUILTIN REWRITE _≡_ #-}

data Bool : Set where true false : Bool

op : Bool → Set → Set
op false _ = Bool
op true  A = A

postulate
  id : Bool → Bool
  id-comp : ∀ y → id y ≡ y
  {-# REWRITE id-comp #-}

postulate
  A : Set
  law : (i : Bool) → op (id i) A ≡ Bool
  {-# REWRITE law #-}

ok : (i : Bool) → op i A ≡ Bool
ok i = refl
