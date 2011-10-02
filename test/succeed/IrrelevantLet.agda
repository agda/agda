-- Andreas, 2011-10-02
module IrrelevantLet where

postulate 
  A : Set

test : (.A → A) → .A → A
test = λ f a →
         let .b : A
             b  = f a
         in  f a
