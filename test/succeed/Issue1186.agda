-- 2014-08-25 reported by Wolfram Kahl, test case shrunk by Ulf, fixed by Andreas and Ulf
-- {-# OPTIONS --show-implicit -v tc.cover.splittree:10 -v tc.with:40 -v tc.cc:12 #-}
postulate K : Set

data SUList : K → Set where
  cons : ∀ {k} (es : SUList k) → SUList k

data Tri : Set where
  tri< tri> : Tri

postulate
  k : K
  compareK : Tri
  dummy : Set
  es : SUList k

diff : SUList k → SUList k → Tri → Set
diff (cons _) _     tri< = K
diff es₁ (cons es₂) tri> = diff es₁ es₂ compareK

test = diff (cons es) (cons es) tri>
-- normalizing  test
-- gives WRONG  diff (cons k es) es compareK
-- should be    diff (cons {k} es) es compareK
-- Problem was in the clause compiler

-- Trigger the bug:
from : (es : SUList k) (c : Tri) → diff (cons es) (cons es) c → Set
from es tri< d = K
from es tri> d with dummy
... | _ = K

-- WAS:
-- Expected a hidden argument, but found a visible argument
-- when checking that the type
-- Set → (es₁ : SUList k) (d : diff (cons k es₁) es₁ compareK) → Set
-- of the generated with function is well-formed
