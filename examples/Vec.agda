module Vec where
  {- Computed datatypes -}
  data One : Set where
    unit : One

  data Nat : Set where 
    zero : Nat 
    suc  : Nat -> Nat

  data _*_ (A B : Set) : Set where
    pair : A -> B -> A * B

  infixr 20 _=>_
  data _=>_ (A B : Set) : Set where
    lam : (A -> B) -> A => B

  lam2 : {A B C : Set} -> (A -> B -> C) -> (A => B => C)
  lam2 f = lam (\x -> lam (f x))

  app : {A B : Set} -> (A => B) -> A -> B
  app (lam f) x =  f x

  Vec : Nat -> Set -> Set
  Vec  zero   X = One
  Vec (suc n) X = X * Vec n X

  {- ... construct the vectors of a given length -}

  vHead : {X : Set} -> (n : Nat)-> Vec (suc n) X -> X
  vHead n (pair a b) = a

  vTail : {X : Set} -> (n : Nat)-> Vec (suc n) X -> Vec n X
  vTail n (pair a b) = b

  {- safe destructors for nonempty vectors -}

  {- useful vector programming operators -}

  vec : {n : Nat}{X : Set} -> X -> Vec n X
  vec {zero } x = unit
  vec {suc n} x = pair x (vec x)

  vapp : {n : Nat}{S T : Set} -> Vec n (S => T) -> Vec n S -> Vec n T
  vapp {zero } unit unit = unit
  vapp {suc n} (pair f fs) (pair s ss) = pair (app f s) (vapp fs ss)

  {- mapping and zipping come from these -}

  vMap : {n : Nat}{S T : Set} -> (S -> T) -> Vec n S -> Vec n T
  vMap f ss = vapp (vec (lam f)) ss

  {- transposition gets the type it deserves -}

  transpose : {m n : Nat}{X : Set} -> Vec m (Vec n X) -> Vec n (Vec m X)
  transpose {zero } xss = vec unit
  transpose {suc m} (pair xs xss) =
    vapp (vapp (vec (lam2 pair)) xs)
         (transpose xss)

  {- Sets of a given finite size may be computed as follows... -}

  {- Resist the temptation to mention idioms. -}

  data Zero : Set where

  data _+_ (A B : Set) : Set where
    inl : A -> A + B
    inr : B -> A + B

  Fin : Nat -> Set
  Fin zero    = Zero
  Fin (suc n) = One + Fin n

  {- We can use these sets to index vectors safely. -}

  vProj : {n : Nat}{X : Set} -> Vec n X -> Fin n -> X
  vProj {zero }  _           ()
  vProj {suc n} (pair x xs) (inl unit) = x
  vProj {suc n} (pair x xs) (inr i)    = vProj xs i

  {- We can also tabulate a function as a vector. Resist
     the temptation to mention logarithms. -}

  vTab : {n : Nat}{X : Set} -> (Fin n -> X) -> Vec n X
  vTab {zero } _ = unit
  vTab {suc n} f = pair (f (inl unit)) (vTab (\x -> f (inr x)))

  {- Question to ponder in your own time:
     if we use functional vectors what are vec and vapp -}

  {- Answer: K and S -}

  {- Inductive datatypes of the unfocused variety -}

  {- Every constructor must target the whole family rather
     than focusing on specific indices. -}

  data Tm (n : Nat) : Set where
    evar : Fin n -> Tm n
    eapp : Tm n -> Tm n -> Tm n
    elam : Tm (suc n) -> Tm n

  {- Renamings -}

  Ren : Nat -> Nat -> Set
  Ren m n = Vec m (Fin n)

  _`Ren`_ = Ren

  {- identity and composition -}

  idR : {n : Nat} -> n `Ren` n
  idR = vTab (\i -> i) 
  
  coR : {l m n : Nat} -> m `Ren` n -> l `Ren` m -> l `Ren` n
  coR m2n l2m = vMap (vProj m2n) l2m

  {- what theorems should we prove -}

  {- the lifting functor for Ren -}

  liftR : {m n : Nat} -> m `Ren` n -> suc m `Ren` suc n
  liftR m2n = pair (inl unit) (vMap inr m2n)

  {- what theorems should we prove -}

  {- the functor from Ren to Tm-arrows -}

  rename : {m n : Nat} -> (m `Ren` n) -> Tm m -> Tm n
  rename m2n (evar i)   = evar (vProj m2n i)
  rename m2n (eapp f s) = eapp (rename m2n f) (rename m2n s)
  rename m2n (elam t)   = elam (rename (liftR m2n) t)

  {- Substitutions -}

  Sub : Nat -> Nat -> Set
  Sub m n = Vec m (Tm n)

  _`Sub`_ = Sub

  {- identity; composition must wait; why -}

  idS : {n : Nat} -> n `Sub` n
  idS = vTab evar

  {- functor from renamings to substitutions -}

  Ren2Sub : {m n : Nat} -> m `Ren` n -> m `Sub` n
  Ren2Sub m2n = vMap evar m2n

  {- lifting functor for substitution -}

  liftS : {m n : Nat} -> m `Sub` n -> suc m `Sub` suc n
  liftS m2n = pair (evar (inl unit))
                       (vMap (rename (vMap inr idR)) m2n)

  {- functor from Sub to Tm-arrows -}

  subst : {m n : Nat} -> m `Sub` n -> Tm m -> Tm n
  subst m2n (evar i)   = vProj m2n i
  subst m2n (eapp f s) = eapp (subst m2n f) (subst m2n s)
  subst m2n (elam t)   = elam (subst (liftS m2n) t)

  {- and now we can define composition -}

  coS : {l m n : Nat} -> m `Sub` n -> l `Sub` m -> l `Sub` n
  coS m2n l2m = vMap (subst m2n) l2m
