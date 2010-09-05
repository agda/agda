{- Agda can check termination of Stream transducer operations.
   (Created: Andreas Abel, 2008-12-01
    at Agda Intensive Meeting 9 in Sendai, Japan.
    I acknowledge the support by AIST and JST.)

Stream transducers have been described in:

  N. Ghani, P. Hancock, and D. Pattinson,
  Continuous functions on final coalgebras.
  In Proc. CMCS 2006, Electr. Notes in Theoret. Comp. Sci., 2006.

They have been modelled by mixed equi-(co)inductive sized types in

  A. Abel,
  Mixed Inductive/Coinductive Types and Strong Normalization.
  In APLAS 2007, LNCS 4807.

Here we model them by mutual data/codata and mutual recursion/corecursion.
Cf. examples/StreamEating.agda
 -}

module StreamProc where

open import Common.Coinduction

data Stream (A : Set) : Set where
  cons : A -> ∞ (Stream A) -> Stream A

-- Stream Transducer: Trans A B
-- intended semantics: Stream A -> Stream B

mutual

  data Trans (A B : Set) : Set where
    〈_〉 : ∞ (Trans' A B) -> Trans A B

  data Trans' (A B : Set) : Set where
    get : (A -> Trans' A B) -> Trans' A B
    put : B -> Trans A B -> Trans' A B

out : forall {A B} -> Trans A B -> Trans' A B
out 〈 p 〉 = p

-- evaluating a stream transducer ("stream eating")

mutual

  -- eat is defined by corecursion into Stream B
  eat  : forall {A B} -> Trans A B -> Stream A -> Stream B
  eat 〈 sp 〉 as ~ eat' sp as

  -- eat' is defined by a local recursion on Trans' A B
  eat' : forall {A B} -> Trans' A B -> Stream A -> Stream B
  eat' (get f) (cons a as) = eat' (f a) as
  eat' (put b sp) as = cons b (eat sp as)


-- composing two stream transducers

mutual

  -- comb is defined by corecursion into Trans A B
  comb : forall {A B C} -> Trans A B -> Trans B C -> Trans A C
  comb 〈 p1 〉 〈 p2 〉 ~ 〈 comb' p1 p2 〉

  -- comb' preforms a local lexicographic recursion on (Trans' B C, Trans' A B)
  comb' : forall {A B C} -> Trans' A B -> Trans' B C -> Trans' A C
  comb' (put b p1) (get f)    = comb' (out p1) (f b)
  comb' (put b p1) (put c p2) = put c (comb p1 p2)
  comb' (get f)    p2         = get (\ a -> comb' (f a) p2)
