
data U : Set
T : U → Set

{-# NO_UNIVERSE_CHECK #-}
data U where
  pi : (A : Set)(b : A → U) → U

T (pi A b) = (x : A) → T (b x)
