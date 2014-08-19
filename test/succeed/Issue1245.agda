module Issue1245 where

postulate
  A B : Set
  [_] : A -> B

module M (_ : B) where

module N (a : A) = M [ a ]
