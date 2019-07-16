{- Jesper, 2019-07-05: At first, the fix to #3859 causes the line below to
raise a type error:

  Cannot instantiate the metavariable _6 to solution Set
  (Agda.Primitive.lsuc (Agda.Primitive.lsuc Agda.Primitive.lzero)
  Agda.Primitive.⊔ Agda.Primitive.lsuc a) since it contains the
  variable a which is not in scope of the metavariable or irrelevant
  in the metavariable but relevant in the solution
  when checking that the expression λ (A : Set a) → Set has type
  (A : Set a) → Set₁

Now it is no longer the case. This test case is here to make sure the
error doesn't come back.
-}

F = λ {a} (A : Set a) → Set
