-- Andreas, 2012-09-11
{-# OPTIONS --show-implicit #-}
-- {-# OPTIONS -v tc.meta:50 #-}
module Const where

import Common.Level

const : {A B : Set} → A → B → A
const a b = a
-- If this is analyzed as {A B : Set} → A → .B → A
-- then, due to constraint solving insensitive to subtyping,
-- the following will trigger an 'UnequalRelevance' error.

postulate
  F : Set → Set
  _<$>_ : {A B : Set} → (A → B) → F A → F B
  _<*>_ : {A B : Set} → F (A → B) → F A → F B

test : {A B : Set} → F A → F B → F A
test {A} {B} x y = (const <$> x) <*> y

