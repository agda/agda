{-# OPTIONS --cubical #-}

mutual
  data Ord : Set
  data _≤_ : Ord -> Ord -> Set

  data Ord where
    succ  : Ord -> Ord
    limit : (x y : Ord) -> (x<y : succ x ≤ y) → Ord

  data _≤_ where
    ≤-limiting  : ∀ x y x<y z -> (limit x y x<y) ≤ z

≤-ind : (P : {x y : Ord} → x ≤ y → Set) →
        (∀ x y x<y z → P x<y → P (≤-limiting x y x<y z)) →
        (x y : Ord) → (x≤y : x ≤ y) → P x≤y
≤-ind P l .(limit x y x<y) .z (≤-limiting x y x<y z) = l x y x<y z (≤-ind P l (succ x) y x<y)
