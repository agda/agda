-- Issue reported by Christian Sattler on 2019-12-02

postulate
  M : Set
  m₀ : M
  D : Set
  d : D
  Y : (m : M) (a : D) → Set
  y : Y m₀ d
  R' : M → Set

data X : M → Set where
  conX : X m₀

R : M → Set
R = R'

postulate
  felt :
      (m : M)
      (f : X m → D)
      (g : (x : X m) → Y m (f x))
    → R m -- No error if R unfolded to R'.

module _ (m : M) where
  foo : R m
  foo = felt _ f g where
    f : X _ → D -- No error if signature of f given as _.
    f conX = d

    g : (x : X _) → Y _ (f x)
    g conX = y -- Accepted if y given as hole filler.

-- WAS: error:
--   d != f conX of type D
--   when checking that the expression y has type Y m₀ (f conX)
-- SHOULD: succeed.
