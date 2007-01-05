module examples.Vec where
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

  vec : {X : Set} -> (n : Nat) -> X -> Vec n X
  vec zero    x = unit
  vec (suc n) x = pair x (vec n x)

  vapp : {S T : Set} -> (n : Nat) -> Vec n (S => T) -> Vec n S -> Vec n T
  vapp zero unit unit = unit
  vapp (suc n) (pair f fs) (pair s ss) = pair (app f s) (vapp n fs ss)

  {- mapping and zipping come from these -}

  vMap : {S T : Set} -> (n : Nat) -> (S -> T) -> Vec n S -> Vec n T
  vMap n f ss = vapp n (vec n (lam f)) ss

  {- transposition gets the type it deserves -}

  transpose : {X : Set} -> (m n : Nat)-> Vec m (Vec n X) -> Vec n (Vec m X)
  transpose zero n xss = vec n unit
  transpose (suc m) n (pair xs xss) =
    vapp n (vapp n (vec n (lam2 pair)) xs)
	   (transpose m n xss)

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

  vProj : {X : Set} -> (n : Nat)-> Vec n X -> Fin n -> X
  -- vProj zero () we can pretend that there is an exhaustiveness check
  vProj (suc n) (pair x xs) (inl unit) = x
  vProj (suc n) (pair x xs) (inr i)    = vProj n xs i

  {- We can also tabulate a function as a vector. Resist
     the temptation to mention logarithms. -}

  vTab : {X : Set} -> (n : Nat)-> (Fin n -> X) -> Vec n X
  vTab zero    _ = unit
  vTab (suc n) f = pair (f (inl unit)) (vTab n (\x -> f (inr x)))

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

  idR : (n : Nat) -> n `Ren` n
  idR n = vTab n (\i -> i) 
  
  coR : (l m n : Nat) -> m `Ren` n -> l `Ren` m -> l `Ren` n
  coR l m n m2n l2m = vMap l (vProj m m2n) l2m

  {- what theorems should we prove -}

  {- the lifting functor for Ren -}

  liftR : (m n : Nat) -> m `Ren` n -> suc m `Ren` suc n
  liftR m n m2n = pair (inl unit) (vMap m inr m2n)

  {- what theorems should we prove -}

  {- the functor from Ren to Tm-arrows -}

  rename : {m n : Nat} -> (m `Ren` n) -> Tm m -> Tm n
  rename {m}{n} m2n (evar i)   = evar (vProj m m2n i)
  rename {m}{n} m2n (eapp f s) = eapp (rename m2n f) (rename m2n s)
  rename {m}{n} m2n (elam t)   = elam (rename (liftR m n m2n) t)

  {- Substitutions -}

  Sub : Nat -> Nat -> Set
  Sub m n = Vec m (Tm n)

  _`Sub`_ = Sub

  {- identity; composition must wait; why -}

  idS : (n : Nat) -> n `Sub` n
  idS n = vTab n (evar {n})

  {- functor from renamings to substitutions -}

  Ren2Sub : (m n : Nat) -> m `Ren` n -> m `Sub` n
  Ren2Sub m n m2n = vMap m evar m2n

  {- lifting functor for substitution -}

  liftS : (m n : Nat) -> m `Sub` n -> suc m `Sub` suc n
  liftS m n m2n = pair (evar (inl unit))
		       (vMap m (rename (vMap n inr (idR n))) m2n)

  {- functor from Sub to Tm-arrows -}

  subst : {m n : Nat} -> m `Sub` n -> Tm m -> Tm n
  subst {m}{n} m2n (evar i)   = vProj m m2n i
  subst {m}{n} m2n (eapp f s) = eapp (subst m2n f) (subst m2n s)
  subst {m}{n} m2n (elam t)   = elam (subst (liftS m n m2n) t)

  {- and now we can define composition -}

  coS : (l m n : Nat) -> m `Sub` n -> l `Sub` m -> l `Sub` n
  coS l m n m2n l2m = vMap l (subst m2n) l2m

