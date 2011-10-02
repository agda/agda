-- Andreas, 2011-10-02
module IrrelevantLambdasDoNotNeedDotsAlways where

bla : ((.Set → Set1) → Set1) -> Set1
bla f = f (λ x → Set)

-- here, the lambda does not need a dot, like in (λ .x → Set)
-- because the dot from the function space can be taken over