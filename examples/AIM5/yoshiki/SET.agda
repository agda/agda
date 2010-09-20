-------------------------------------------------------------------------------

--
-- SET (in Hedberg library) for agda2
--  as of 2006.9.29 morning
--  Yoshiki.
--
module SET where
  ----------------------------------------------------------------------------
  -- Auxiliary.
  ----------------------------------------------------------------------------
  -- no : (x : A) -> B : Set  if A : Set B : Set
  -- yes : (x : A) -> B type   if A type  B type
  -- El M type   if  M : Set

  data Unop (A : Set) : Set1 where
    unopI : (A -> A) -> Unop A
  data Pred (A : Set) : Set1 where
    PredI : (A -> Set) -> Pred A
  data Rel (A : Set) : Set1 where
    RelI : (A -> A -> Set) -> Rel A
  data Reflexive {A : Set} (R : A -> A -> Set) : Set where
    reflexiveI : ((a : A) -> R a a) -> Reflexive R
  data Symmetrical {A : Set} (R : A -> A -> Set) : Set where
    symmetricalI : ({a b : A} -> R a b -> R a b) -> Symmetrical R
  data Transitive {A : Set} (R : A -> A -> Set) : Set where
    transitiveI : ({a b c : A} -> R a b -> R b c -> R a c) -> Transitive R
  compositionalI : 
    {A : Set} -> (R : A -> A -> Set)
    -> ({a b c : A} -> R b c -> R a b -> R a c) -> Transitive R
  compositionalI {A} R f =
    transitiveI (\{a b c : A} -> \(x : R a b) -> \(y : R b c) -> f y x)
  data Substitutive {A : Set} (R : A -> A -> Set) : Set1 where
    substitutiveI : ((P : A -> Set) -> {a b : A} -> R a b -> P a -> P b)
                   -> Substitutive R
  data Collapsed (A : Set) : Set1 where
    collapsedI : ((P : A -> Set) -> {a b : A} -> P a -> P b) -> Collapsed A

  cmp : {A B C : Set} -> (B -> C) -> (A -> B) -> A -> C
  cmp f g a = f (g a)
  seq : {A B C : Set} -> (A -> B) -> (B -> C) -> A -> C
  seq f g = cmp g f

  S : {A B C : Set} -> (C -> B -> A) -> (C -> B) -> C -> A
  S x y z = x z (y z)
  K : {A B : Set} -> A -> B -> A
  K x y = x
  I : {A : Set} -> A -> A
  I a = a
  -- of course I = S K K

  id = \{A : Set} -> I {A}

  const = \{A B : Set} -> K {A}{B}

  -- Set version
  pS : {P Q R : Set} -> (R -> Q -> P) -> (R -> Q) -> R -> P
  pS x y z = x z (y z)
  pK : {P Q : Set} -> P -> Q -> P
  pK x y = x
  pI : {P : Set} -> P -> P
  pI a = a

  proj : {A : Set} -> (B : A -> Set) -> (a : A) -> (f : (aa : A) -> B aa) -> B a
  proj B a f = f a

  flip : {A B C : Set} (f : A -> B -> C) (b : B) (a : A) -> C
  flip f b a = f a b

  -- separate definition of FlipRel is necessary because it is not the case
  -- that Set : Set.
  FlipRel : {A : Set} -> (R : A -> A -> Set) -> (a b : A) -> Set
  FlipRel R a b = R b a

  ----------------------------------------------------------------------------
  -- Product sets.
  ----------------------------------------------------------------------------
--  Prod : (A : Set) -> (A -> Set) -> Set
--  Prod A B = (a : A) -> B a
--  The above is not type-correct since (a : A) -> B a is not well-formed 
--  but the following works.
  data Prod (A : Set) (B : A -> Set) : Set where
    prodI : ((a : A) -> B a) -> Prod A B
  mapProd : {A : Set} -> {B C : A -> Set} -> ((a : A) -> B a -> C a)
           -> Prod A B -> Prod A C
  mapProd {A} f (prodI g) = prodI (\(a : A) -> f a (g a))

--  data Fun (A B : Set) : Set1 where
--    funI : (A -> B) -> Fun A B
  Fun : Set -> Set -> Set
  Fun A B = Prod A (\(_ : A) -> B)

  mapFun : {A B C D : Set} -> (B -> A) -> (C -> D) -> (A -> C) -> B -> D
  mapFun {A} {B} {C} {D} f g h x = g (h (f x))
--  mapFun (|X1 |X2 |Y1 |Y2 :: Set)
--    :: (X2 -> X1) -> (Y1 -> Y2) -> (X1 -> Y1) -> X2 -> Y2
--    = \f -> \g -> \h -> \x ->
--      g (h (f x))


---------------------------------------------------------------------------
-- Identity proof sets.
---------------------------------------------------------------------------
-- to accept the following definition more general scheme of
-- inductive definition is required
--  data Id (A : Set) (a b : A) : Set1 where
--    ref : (a : A) -> Id A a a
--
--  elimId (|X :: Set)
--         (C :: (x1 x2 :: X)  |-> Id x1 x2 -> Set)
--         (refC :: (x :: X) -> C (refId x))
--         (|x1 |x2 :: X)
--         (u :: Id x1 x2) ::
--         C u
--    = case u of { (ref x) -> refC x;}
--
--  abstract whenId (|X :: Set)(C :: Rel X)(c :: (x :: X) -> C x x)
--    :: (x1 x2 :: X)  |-> Id x1 x2 -> C x1 x2
--    = elimId (\x1 x2 |-> \(u :: Id x1 x2) -> C x1 x2) c
--
--  abstract substId (|X :: Set) :: Substitutive Id
--    = \(C :: Pred X) ->
--      whenId (\x1 x2 -> C x1 -> C x2) (\x -> id)
--
--  abstract mapId (|X :: Set)(|Y :: Set)(f :: X -> Y)
--    :: (x1 x2 :: X) |-> Id x1 x2 -> Id (f x1) (f x2)
--    = whenId (\x1 x2 -> Id (f x1) (f x2)) (\(x :: X) -> refId (f x))
--
--  abstract symId (|X :: Set) :: Symmetrical Id
--    =  whenId (\(x1 x2 :: X) ->  Id x2 x1) refId
--
--  abstract cmpId (|X :: Set) :: Compositional Id
--    = let lem :: (x y :: X) |-> Id x y -> (z :: X) |-> Id z x -> Id z y
--            = whenId ( \(x y :: _) -> (z :: X) |-> Id z x -> Id z y)
--                     ( \x -> \z |-> id)
--      in  \(x1 x2 x3 :: _) |->
--          \(u :: Id x2 x3) ->
--          \(v :: Id x1 x2) ->
--          lem  u v
--
--  abstract tranId (|X :: Set) :: Transitive  Id
--    = \(x1 x2 x3 :: X) |->
--      \(u :: Id x1 x2) ->
--      \(v :: Id x2 x3) ->
--      cmpId v u

  ----------------------------------------------------------------------------
  -- The empty set.
  ----------------------------------------------------------------------------
  data Zero : Set where
--  --abstract whenZero (X :: Set)(z :: Zero) :: X
--  --  = case z of { }
--  do not know how to encode whenZero;  the following does not work.
--  whenZero : (X : Set) -> (z : Zero) -> X
--  whenZero X z =
--  --elimZero (C :: Zero -> Set)(z :: Zero) :: C z
--  --  = case z of { }
--  elimZero either!
--  elimZero : (C : Zero -> Set) -> (z : Zero) -> C z
--  elimZero C z =
--
--  abstract collZero :: Collapsed Zero
--    = \(C :: Zero -> Set) ->
--      \(z1 z2 :: Zero) |->
--      \(c :: C z1) ->
--      case z1 of { }
--
----------------------------------------------------------------------------
-- The singleton set.
----------------------------------------------------------------------------
  data Unit : Set where
    uu : Unit
  elUnit = uu
  elimUnit : (C : Unit -> Set) -> C uu -> (u : Unit) -> C u
  elimUnit C c uu = c
--  Do not know of the exact use of Collapse!
--  collUnit : (C : Unit -> Set) -> {u1  u2 : Unit} -> C u1 -> Collapsed Unit
--  collUnit C {uu} {uu} A = collapsedI (\(P : Unit -> Set) -> \{a b : Unit} -> \(y : P a) -> A)
--  abstract collUnit :: Collapsed Unit
--    = \(C :: Unit -> Set) ->
--      \(u1 u2 :: Unit) |->
--      \(c :: C u1) ->
--      case u1 of { (tt) -> case u2 of { (tt) -> c;};}
---------------------------------------------------------------------------
-- The successor set adds a new element.
---------------------------------------------------------------------------

  data Succ (A : Set) : Set where
    zerS : Succ A
    sucS : A -> Succ A
  zerSucc = \{A : Set} -> zerS {A}
  sucSucc = \{A : Set} -> sucS {A}
  elimSucc : {X : Set} -> (C : Succ X -> Set)
            -> C zerS -> ((x : X) -> C (sucS x)) -> (xx : Succ X) -> (C xx)
  elimSucc C c_z c_s zerS = c_z
  elimSucc C c_z c_s (sucS x) = c_s x
  whenSucc : {X Y : Set} -> Y -> (X -> Y) -> (Succ X) -> Y
  whenSucc y_z y_s zerS = y_z
  whenSucc y_z y_s (sucS x) = y_s x
  mapSucc : {X Y : Set} -> (X -> Y) -> Succ X -> Succ Y
  mapSucc {X} {_} f
    = whenSucc zerS (\(x : X) -> sucS (f x))

---------------------------------------------------------------------------
-- The (binary) disjoint union.
---------------------------------------------------------------------------

  data Plus (A B : Set) : Set where
    inl : A -> Plus A B
    inr : B -> Plus A B
  elimPlus : {X Y : Set} ->
            (C : Plus X Y -> Set) ->
            ((x : X) -> C (inl x)) ->
            ((y : Y) -> C (inr y)) ->
            (z : Plus X Y) ->
            C z
  elimPlus {X} {Y} C c_lft c_rgt (inl x) = c_lft x
  elimPlus {X} {Y} C c_lft c_rgt (inr x) = c_rgt x
  when : {X Y Z : Set} -> (X -> Z) -> (Y -> Z) -> Plus X Y -> Z
  when {X} {Y} {Z} f g (inl x) = f x
  when {X} {Y} {Z} f g (inr y) = g y
  whenplus : {X Y Z : Set} -> (X -> Z) -> (Y -> Z) -> Plus X Y -> Z
  whenplus = when
  mapPlus : {X1 X2 Y1 Y2 : Set} -> (X1 -> X2) -> (Y1 -> Y2)
           -> Plus X1 Y1 -> Plus X2 Y2
  mapPlus f g = when (\x1 -> inl (f x1)) (\y1 -> inr (g y1))
  swapPlus : {X Y : Set} -> Plus X Y -> Plus Y X
  swapPlus = when inr inl

----------------------------------------------------------------------------
-- Dependent pairs.
----------------------------------------------------------------------------

  data Sum (A : Set) (B : A -> Set) : Set where
    sumI : (fst : A) -> B fst -> Sum A B
  depPair : {A : Set} -> {B : A -> Set} -> (a : A) -> B a -> Sum A B
  depPair a b = sumI a b
  depFst : {A : Set} -> {B : A -> Set} -> (c : Sum A B) -> A
  depFst (sumI fst snd) = fst
  depSnd : {A : Set} -> {B : A -> Set} -> (c : Sum A B) -> B (depFst c)
  depSnd (sumI fst snd) = snd
  depCur : {A : Set} -> {B : A -> Set} -> {C : Set} -> (f : Sum A B -> C)
           -> (a : A) -> B a -> C
  depCur f = \a -> \b -> f (depPair a b)
  -- the above works but the below does not---why?
  -- depCur : {X : Set} -> {Y : X -> Set} -> {Z : Set} -> (f : Sum X Y -> Z)
  --         -> {x : X} -> Y x -> Z
  -- depCur {X} {Y} {Z} f = \{x} -> \y ->  f (depPair  x  y)
  -- Error message : 
  -- When checking that the expression \{x} -> \y -> f (depPair x y)
  -- has type Y _x -> Z
  -- found an implicit lambda where an explicit lambda was expected
  depUncur : {A : Set} -> {B : A -> Set} -> {C : Set}
    -> ((a : A) -> B a -> C) -> Sum A B -> C
  depUncur f ab = f (depFst ab) (depSnd ab)
  depCurry : {A : Set} ->
             {B : A -> Set} ->
             {C : Sum A B -> Set} ->
             (f : (ab : Sum A B) -> C ab) ->
             (a : A) ->
             (b : B a) ->
             C (depPair a b)
  depCurry f a b = f (depPair a b)
  depUncurry : {A : Set} ->
               {B : A -> Set} ->
               {C : Sum A B -> Set} ->
               (f : (a : A) -> (b : B a) -> C (depPair a b)) ->
               (ab : Sum A B) ->
               C ab
  depUncurry f (sumI fst snd) = f fst snd
  mapSum : {A : Set} -> {B1 : A -> Set} -> {B2 : A -> Set}
          -> (f : (a : A) -> B1 a -> B2 a)
          -> Sum A B1 -> Sum A B2
  mapSum f (sumI fst snd) = depPair fst (f fst snd)
  elimSum = \{A : Set}{B : A -> Set}{C : Sum A B -> Set} -> depUncurry{A}{B}{C}
---------------------------------------------------------------------------
-- Nondependent pairs (binary) cartesian product.
---------------------------------------------------------------------------
  Times : Set -> Set -> Set
  Times A B = Sum A (\(_ : A) -> B)
  pair : {A : Set} -> {B : Set} -> A -> B -> Times A B
  pair a b = sumI a b
  fst : {A : Set} -> {B : Set} -> Times A B -> A
  fst (sumI a _) = a
  snd : {A : Set} -> {B : Set} -> Times A B -> B
  snd (sumI _ b) = b
  pairfun : {C : Set} -> {A : Set} -> {B : Set}
           -> (C -> A) -> (C -> B) -> C -> Times A B
  pairfun f g c = pair (f c) (g c)
  mapTimes : {A1 : Set} -> {A2 : Set} -> {B1 : Set} -> {B2 : Set}
            -> (A1 -> A2) -> (B1 -> B2) -> Times A1 B1 -> Times A2 B2
  mapTimes f g (sumI a b) = pair (f a) (g b)
  swapTimes : {A : Set} -> {B : Set} -> Times A B -> Times B A
  swapTimes (sumI a b) = sumI b a
  cur : {A : Set} -> {B : Set} -> {C : Set} -> (f : Times A B -> C) -> A -> B -> C
  cur f a b = f (pair a b)
  uncur : {A : Set} -> {B : Set} -> {C : Set} -> (A -> B -> C) -> Times A B -> C
  uncur f (sumI a b) = f a b
  curry : {A : Set} -> {B : Set} -> {C : Times A B -> Set}
         -> ((p : Times A B) -> C p) -> (a : A) ->(b : B) -> C (pair a b)
  curry f a b = f (pair a b)
  uncurry : {A : Set} -> {B : Set} -> {C : Times A B -> Set}
           -> ((a : A) -> (b : B) -> C (pair a b)) -> (p : Times A B) -> C p
  uncurry f (sumI a b) = f a b
  elimTimes = \{A B : Set}{C : Times A B -> Set} -> uncurry{A}{B}{C}
  ---------------------------------------------------------------------------
  -- Natural numbers.
  ---------------------------------------------------------------------------
  data Nat : Set where
    zero : Nat
    succ : Nat -> Nat
  elimNat : (C : Nat -> Set)
           -> (C zero) -> ((m : Nat) -> C m -> C (succ m)) -> (n : Nat) -> C n
  elimNat C c_z c_s zero = c_z
  elimNat C c_z c_s (succ m') = c_s m' (elimNat C c_z c_s m')

  ----------------------------------------------------------------------------
  -- Linear universe of finite sets.
  ----------------------------------------------------------------------------
  Fin : (m : Nat) -> Set
  Fin zero = Zero
  Fin (succ n) = Succ (Fin n)
{-
  Fin 0 = {}
  Fin 1 = { zerS }
  Fin 2 = { zerS (sucS zerS) }
  Fin 3 = { zerS (sucS zerS) (sucS (sucS zerS)) }
-}
  valFin : (n' : Nat) -> Fin n' -> Nat
  valFin zero     ()
  valFin (succ n) zerS = zero
  valFin (succ n) (sucS x) = succ (valFin n x)
  zeroFin : (n : Nat) -> Fin (succ n)
  zeroFin n = zerS
  succFin : (n : Nat) -> Fin n -> Fin (succ n)
  succFin n N = sucS N
  ----------------------------------------------------------------------------
  -- Do these really belong here?
  ----------------------------------------------------------------------------
  HEAD : {A : Set} -> (n : Nat) -> (Fin (succ n) -> A) -> A
  HEAD n f = f (zeroFin n)
  TAIL : {A : Set} -> (n : Nat) -> (Fin (succ n) -> A) -> Fin n -> A
  TAIL n f N = f (succFin n N)
  ----------------------------------------------------------------------------
  -- Lists.
  ----------------------------------------------------------------------------
  data List (A : Set) : Set where
    nil : List A
    con : A -> List A -> List A
  elimList : {A : Set} ->
            (C : List A -> Set) ->
            (C nil) ->
            ((a : A) -> (as : List A) -> C as -> C (con a as)) ->
            (as : List A) ->
            C as
  elimList _ c_nil _ nil = c_nil
  elimList C c_nil c_con (con a as) = c_con a as (elimList C c_nil c_con as)
  ----------------------------------------------------------------------------
  -- Tuples are "dependently typed vectors".
  ----------------------------------------------------------------------------
  data Nill : Set where
    nill : Nill
  data Cons (A B : Set) : Set where
    cons : A -> B -> Cons A B
  Tuple : (n : Nat) -> (C : Fin n -> Set) -> Set
  Tuple zero = \ C -> Nill
  Tuple (succ n) = \ C -> Cons (C zerS) (Tuple n (\(N : Fin n) -> C (sucS N)))
  ----------------------------------------------------------------------------
  -- Vectors homogeneously typed tuples.
  ----------------------------------------------------------------------------
  Vec : Set -> Nat -> Set
  Vec A m = Tuple m (\(n : Fin m) -> A)
  ----------------------------------------------------------------------------
  -- Monoidal expressions.
  ----------------------------------------------------------------------------
  data Mon (A : Set) : Set where
    unit : Mon A
    at : A -> Mon A
    mul : Mon A -> Mon A -> Mon A
{-
-}

----------------------------------------------------------------------------
-- Propositions.
----------------------------------------------------------------------------
  data Implies (A B : Set) : Set where
    impliesI : (A -> B) -> Implies A B
  data Absurd : Set where
  data Taut : Set where
    tt : Taut
  data Not (P : Set) : Set where
    notI : (P -> Absurd) -> Not P
  -- encoding of Exists is unsatisfactory!  Its type should be Set.
  data Exists (A : Set) (P : A -> Set) : Set where
    existsI : (evidence : A) -> P evidence -> Exists A P
  data Forall (A : Set) (P : A -> Set) : Set where
    forallI : ((a : A) -> P a) -> Forall A P
  data And (A B : Set) : Set where
    andI : A -> B -> And A B
  Iff : Set -> Set -> Set
  Iff A B = And (Implies A B) (Implies B A)
  data Or (A B : Set) : Set where
    orIl : (a : A) -> Or A B
    orIr : (b : B) -> Or A B
  Decidable : Set -> Set
  Decidable P = Or P (Implies P Absurd)
  data DecidablePred {A : Set} (P : A -> Set) : Set where
   decidablepredIl : (a : A) -> (P a) -> DecidablePred P
   decidablepredIr : (a : A) -> (Implies (P a) Absurd) -> DecidablePred P
  data DecidableRel {A : Set} (R : A -> A -> Set) : Set where
   decidablerelIl : (a b : A) -> (R a b) -> DecidableRel R
   decidablerelIr : (a b : A) -> (Implies (R a b) Absurd) -> DecidableRel R
  data Least {A : Set} (_<=_ : A -> A -> Set) (P : A -> Set) (a : A) : Set where
    leastI : (P a) -> ((aa : A) -> P aa -> (a <= aa)) -> Least _<=_ P a
  data Greatest {A : Set} (_<=_ : A -> A -> Set) (P : A -> Set) (a : A) : Set where
    greatestI : (P a) -> ((aa : A) -> P aa -> (aa <= a)) -> Greatest _<=_ P a

----------------------------------------------------------------------------
-- Booleans.
----------------------------------------------------------------------------
  data Bool : Set where
    true : Bool
    false : Bool
  elimBool : (C : Bool -> Set) -> C true -> C false -> (b : Bool) -> C b
  elimBool C c_t c_f true = c_t
  elimBool C c_t c_f false = c_f
  whenBool : (C : Set) -> C -> C -> Bool -> C
  whenBool C c_t c_f b = elimBool (\(_ : Bool) -> C) c_t c_f b
  data pred (A : Set) : Set where
    predI : (A -> Bool) -> pred A
  data rel (A : Set) : Set where
    relI : (A -> A -> Bool) -> rel A
  True : Bool -> Set
  True true = Taut
  True false = Absurd
  bool2set = True
  pred2Pred : {A : Set} -> pred A -> Pred A
  pred2Pred (predI p) = PredI (\a -> True (p a))
  rel2Rel : {A : Set} -> rel A -> Rel A
  rel2Rel (relI r) = RelI (\a -> \b -> True (r a b))
--  decTrue : (p : Bool) -> Decidable (True p)
--  decTrue true = orIl tt
--  decTrue false = orIr (impliesI pI)
-- decTrue false = orIr (impliesI (\(p : (True false)) -> p))
--  dec_lem : {P : Set} -> (decP : Decidable P)
--           -> Exists A
{-
  abstract dec_lem (|P :: Set)(decP :: Decidable P)
    :: Exist |_ (\(b :: Bool) -> Iff (True b) P)
    = case decP of {
        (inl trueP) ->
          struct {
            fst = true@_;
            snd =
              struct {
                fst = const |_  |_ trueP;  -- (True true@_)
                snd = const |_ |_  tt;};};
        (inr notP) ->
          struct {
            fst = false@_;
            snd =
              struct {
                fst = whenZero P;
                snd = notP;};};}
  dec2bool :: (P :: Set) |-> (decP :: Decidable P) -> Bool
    = \(P :: Set) |-> \(decP :: Decidable P) -> (dec_lem |_ decP).fst
  dec2bool_spec (|P :: Set)(decP :: Decidable P)
    :: Iff (True (dec2bool |_ decP)) P
    = (dec_lem |_ decP).snd

  abstract collTrue :: (b :: Bool) -> Collapsed (True b)
    = let aux (X :: Set)(C :: X -> Set)
            :: (b :: Bool) ->
               (f :: True b -> X) ->
               (t1 :: True b) |->
               (t2 :: True b) |->
               C (f t1) -> C (f t2)
            = \(b :: Bool) ->
              case b of {
                (true) ->
                  \(f :: (x :: True true@_) -> X) ->
                  \(t1 t2 :: True true@_) |->
                  \(c :: C (f t1)) ->
                  case t1 of { (tt) -> case t2 of { (tt) -> c;};};
                (false) ->
                  \(f :: (x :: True false@_) -> X) ->
                  \(t1 t2 :: True false@_) |->
                  \(c :: C (f t1)) ->
                  case t1 of { };}
      in   \(b :: Bool) ->  \(P :: True b -> Set) -> aux (True b) P b id

  bool2nat (p :: Bool) :: Nat
    = case p of {
        (true) -> succ zero;
        (false) -> zero;}
-}

