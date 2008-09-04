module Mixed where

codata Stream (A : Set) : Set where
  cons : A -> Stream A -> Stream A

mutual

  -- inductive version of stream processor
  data SP' (A B : Set) : Set where
    get         : (A -> SP' A B) -> SP' A B
    doneGetting : SP A B -> SP' A B

  codata SP (A B : Set) : Set where
    put : B -> SP' A B -> SP A B

mutual

  eat' : {A B : Set} -> SP' A B -> Stream A -> Stream B
  eat' (get f) (cons a as) = eat' (f a) as
  eat' (doneGetting sp) as = eat sp as

  eat  : {A B : Set} -> SP  A B -> Stream A -> Stream B
  eat (put b sp') as ̃ cons b (eat' sp' as)

