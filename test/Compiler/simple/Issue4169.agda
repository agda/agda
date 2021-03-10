-- Andreas, 2019-11-07, issue #4169 report and testcase by nad.
-- Extra coercions needed when erased versions of functions are used.

open import Agda.Builtin.Unit
open import Common.IO

data D : Set where
  c : D

F : D → Set → Set
F c A = A → A

f : (d : D) (A : Set) → F d A → A → A    -- 14
f c A g = g

f′ : (d : D) (A : Set) (P : Set → Set)   -- 30
     (g : (A : Set) → F d (P A))
   → P A → P A
f′ d A P g = f d (P A) (g A)

module _ (id : (A : Set) → (A → A) → A → A) (G : Set → Set) where

  postulate
    g : (A : Set) → G A → G A

  g′ : (A : Set) → G A → G A
  g′ A s = g A s

  g″ : (A : Set) → G A → G A
  g″ A = id (G A) (f′ c A G g′)

main : IO ⊤
main = return _
