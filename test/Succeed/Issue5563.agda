module Issue5563 where

F : (@0 A : Set) → A → A
F A x =
  let
    y : A
    y = x
  in y
