-- Andreas, 2011-05-09
-- {-# OPTIONS -v tc.meta:15 -v tc.inj:40 #-}
module Issue383 where

data D (A : Set) : A → Set where

data Unit : Set where
  unit : Unit

D′ : (A : Set) → A → Unit → Set
D′ A x unit = D A x

postulate
  Q : (A : Set) → A → Set
  q : (u : Unit) (A : Set) (x : A) → D′ A x u → Q A x

  A : Set
  x : A
  d : D A x

  P : (A : Set) → A → Set
  p : P (Q _ _) (q _ _ _ d)

-- SOLVED, WORKS NOW.
-- OLD BEHAVIOR:
-- Agda does not infer the values of the underscores on the last line.
-- Shouldn't constructor-headedness come to the rescue here? Agda does
-- identify D′ as being constructor-headed, and does invert D′ /six
-- times/, but still fails to infer that the third underscore should
-- be unit.

{-
blocked _41 := d
     by [(D A x) =< (D′ _39 _40 _38) : Set]
blocked _42 := q _38 _36 _40 _41
     by [_40 == _37 : _36]
-}
