module StreamProcEat where

codata Stream (A : Set) : Set where
  cons : A -> Stream A -> Stream A

mutual

  -- Stream Transducer 
  -- intended semantics: Stream A -> Stream B

  codata Trans (A B : Set) : Set where
    〈_〉 : Trans' A B -> Trans A B

  data Trans' (A B : Set) : Set where
    get : (A -> Trans' A B) -> Trans' A B
    put : B -> Trans A B -> Trans' A B
  
out : forall {A B} -> Trans A B -> Trans' A B
out 〈 p 〉 = p 

mutual 

  eat  : forall {A B} -> Trans A B -> Stream A -> Stream B
  eat 〈 sp 〉 as ~ eat' sp as

  eat' : forall {A B} -> Trans' A B -> Stream A -> Stream B
  eat' (get f) (cons a as) = eat' (f a) as
  eat' (put b sp) as = cons b (eat sp as)


mutual

  comb : forall {A B C} -> Trans A B -> Trans B C -> Trans A C
  comb 〈 p1 〉 〈 p2 〉 ~ 〈 comb' p1 p2 〉

  comb' : forall {A B C} -> Trans' A B -> Trans' B C -> Trans' A C
  comb' (put b p1) (get f)    = comb' (out p1) (f b)
  comb' (put b p1) (put c p2) = put c (comb p1 p2)
  comb' (get f)    p2         = get (\ a -> comb' (f a) p2)
