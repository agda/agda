module Issue1245AmbiguousParse where

postulate
  A : Set
  *_* : A → A
  _*_ : A → A → A

module M (_ : A) where

module N (a : A) = M * a * a * a *
