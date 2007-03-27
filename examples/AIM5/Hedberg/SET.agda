module SET where
  ----------------------------------------------------------------------------
  -- Auxiliary.
  ----------------------------------------------------------------------------
  data Fun (X Y : Set) : Set where
    fun : (X -> Y) -> Fun X Y

  {-
  Unop : Set -> Set
  Unop X = Fun X X

  Binop : Set -> Set
  Binop X = Fun X (Fun X X)
  -}

  -- We need to replace Pred X by its RHS (less readable!)

--  Pred : Set -> Set1
--  Pred X = X -> Set
--  Pow = Pred
--  Rel : Set -> Set1
--  Rel X = X -> X -> Set
  data Reflexive {X : Set} (R : X -> X -> Set) : Set where
    reflexive : ((x : X) -> R x x) -> Reflexive R

  data Symmetrical {X : Set} (R : X -> X -> Set) : Set where
    symmetrical : ( {x1 x2 : X} -> R x1 x2 -> R x2 x1) -> Symmetrical R
{-
  Transitive {X : Set}(R : X -> X -> Set) : Set
    = (x1 x2 x3 : X) |->  R x1 x2 -> R x2 x3 -> R x1 x3
  Compositional {X : Set}(R : X -> X -> Set) : Set
    = (x1 : X) |-> (x2 : X) |-> (x3 : X) |-> R x2 x3 -> R x1 x2 -> R x1 x3
-}
  data Substitutive {X : Set} (R : X -> X -> Set) : Set1 where
    substitutive : ( (P : X -> Set) -> {x1 x2 : X} -> R x1 x2 -> P x1 -> P x2)
                   -> Substitutive R
{-
  Collapsed (X : Set) : Set1
    = (P : X -> Set) -> (x1 x2 : X) |-> P x1 -> P x2
  id {X : Set} : X -> X
    = \x -> x
  cmp (|X |Y |Z : Set) : (Y -> Z) -> (X -> Y) -> X -> Z
    = \f -> \g -> \x -> f (g x)
  seq (|X |Y |Z : Set)(f : X -> Y)(g : Y -> Z) : X -> Z
    = cmp g f

  const (|X |Y : Set)(x : X)(y : Y) : X
    = x
  proj {X : Set}(Y : X -> Set)(x : X)(f : (x : X) -> Y x) : Y x
    = f x
  flip {X : Set}{Y : Set}{Z : Set}(f : X -> Y -> Z)(y : Y)(x : X) : Z
    = f x y
  FlipRel {X : Set}(R : X -> X -> Set)(x1 : X)(x2 : X) : Set
    = R x2 x1

  ----------------------------------------------------------------------------
  -- Product sets.
  ----------------------------------------------------------------------------
  Prod (X : Set)(Y : X -> Set) : Set
    = (x : X) -> Y x
  mapProd {X : Set}
          {Y1 : X -> Set}
          {Y2 : X -> Set}
          (f : (x : X) -> Y1 x -> Y2 x)
    : Prod X Y1  -> Prod X Y2
    = \g -> \x -> f x (g x)
  -- Fun(X : Set)(Y : Set) = X -> Y
  mapFun (|X1 |X2 |Y1 |Y2 : Set)
    : (X2 -> X1) -> (Y1 -> Y2) -> (X1 -> Y1) -> X2 -> Y2
    = \f -> \g -> \h -> \x ->
      g (h (f x))

  ----------------------------------------------------------------------------
  -- Identity proof sets.
  ----------------------------------------------------------------------------
  Id {X : Set} : X -> X -> Set
    = idata ref (x : X) : _ x x
  refId {X : Set} : Reflexive Id
    = \(x : X) -> ref@_  x

  elimId (|X : Set)
         (C : (x1 x2 : X)  |-> Id x1 x2 -> Set)
         (refC :  (x : X) -> C (refId x))
         (|x1 |x2 : X)
         (u : Id x1 x2) :
         C u
    = case u of { (ref x) -> refC x;}

  abstract whenId {X : Set}(C : X -> X -> Set)(c : (x : X) -> C x x)
    : (x1 x2 : X)  |-> Id x1 x2 -> C x1 x2
    = elimId (\x1 x2 |-> \(u : Id x1 x2) -> C x1 x2) c

  abstract substId {X : Set} : Substitutive Id
    = \(C : X -> Set) ->
      whenId (\x1 x2 -> C x1 -> C x2) (\x -> id)

  abstract mapId {X : Set}{Y : Set}(f : X -> Y)
    : (x1 x2 : X) |-> Id x1 x2 -> Id (f x1) (f x2)
    = whenId (\x1 x2 -> Id (f x1) (f x2)) (\(x : X) -> refId (f x))

  abstract symId {X : Set} : Symmetrical Id
    =  whenId (\(x1 x2 : X) ->  Id x2 x1) refId

  abstract cmpId {X : Set} : Compositional Id
    = let lem : (x y : X) |-> Id x y -> (z : X) |-> Id z x -> Id z y
            = whenId ( \(x y : _) -> (z : X) |-> Id z x -> Id z y)
                     ( \x -> \z |-> id)
      in  \(x1 x2 x3 : _) |->
          \(u : Id x2 x3) ->
          \(v : Id x1 x2) ->
          lem  u v

  abstract tranId {X : Set} : Transitive  Id
    = \(x1 x2 x3 : X) |->
      \(u : Id x1 x2) ->
      \(v : Id x2 x3) ->
      cmpId v u

  ----------------------------------------------------------------------------
  -- The empty set.
  ----------------------------------------------------------------------------
-}
  data Zero : Set where

{-
  abstract whenZero (X : Set)(z : Zero) : X
    = case z of { }
  elimZero (C : Zero -> Set)(z : Zero) : C z
    = case z of { }
  abstract collZero : Collapsed Zero
    = \(C : Zero -> Set) ->
      \(z1 z2 : Zero) |->
      \(c : C z1) ->
      case z1 of { }
  ----------------------------------------------------------------------------
  -- The singleton set.
  ----------------------------------------------------------------------------
-}
  data Unit : Set where
    unit : Unit
{-
  elUnit = tt
  elimUnit (C : Unit -> Set)(c_tt : C tt@_)(u : Unit) : C u
    = case u of { (tt) -> c_tt;}
  abstract collUnit : Collapsed Unit
    = \(C : Unit -> Set) ->
      \(u1 u2 : Unit) |->
      \(c : C u1) ->
      case u1 of { (tt) -> case u2 of { (tt) -> c;};}
  ----------------------------------------------------------------------------
  -- The successor set adds a new element.
  ----------------------------------------------------------------------------

  Succ (X : Set) : Set
    = data zer | suc (x : X)
  zerSucc {X : Set} : Succ X
    = zer@_
  sucSucc {X : Set}(x : X) : Succ X
    = suc@_ x
  elimSucc {X : Set}
           (C : Succ X -> Set)
           (c_z : C zer@_)
           (c_s : (x : X) -> C (suc@_ x))
           (x' : Succ X)
    : C x'
    = case x' of {
        (zer) -> c_z;
        (suc x) -> c_s x;}
  whenSucc (|X |Y : Set)(y_z : Y)(y_s : X -> Y)(x' : Succ X) : Y
    = case x' of {
        (zer) -> y_z;
        (suc x) -> y_s x;}
  mapSucc (|X |Y : Set)(f : X -> Y) : Succ X -> Succ Y
    = whenSucc zer@(Succ Y) (\(x : X) -> suc@_ (f x)) -- (Succ Y)


  ----------------------------------------------------------------------------
  -- The (binary) disjoint union.
  ----------------------------------------------------------------------------
  data Plus (X Y : Set) = inl (x : X) | inr (y : Y)

  elimPlus (|X |Y : Set)
           (C : Plus X Y -> Set)
           (c_lft : (x : X) -> C (inl@_ x))
           (c_rgt : (y : Y) -> C (inr@_ y))
           (xy : Plus X Y)
    : C xy
    = case xy of {
        (inl x) -> c_lft x;
        (inr y) -> c_rgt y;}
  when (|X |Y |Z : Set)(f : X -> Z)(g : Y -> Z) : Plus X Y -> Z
    = \xy -> case xy of {
        (inl x) -> f x;
        (inr y) -> g y;}
  whenPlus = when
  mapPlus (|X1 |X2 |Y1 |Y2 : Set)(f : X1 -> X2)(g : Y1 -> Y2)
    : Plus X1 Y1 -> Plus X2 Y2
    = when (\x1 -> inl (f x1)) (\y1 -> inr (g y1))
  swapPlus (|X |Y : Set) :  Plus X Y -> Plus Y X
    = when inr inl

  ----------------------------------------------------------------------------
  -- Dependent pairs.
  ----------------------------------------------------------------------------
  Sum (X : Set)(Y : X -> Set) : Set
    = sig{fst : X;
          snd : Y fst;}
  dep_pair {X : Set}{Y : X -> Set}(x : X)(y : Y x) : Sum X Y
    = struct {fst = x; snd = y;}
  dep_fst {X : Set}{Y : X -> Set}(xy : Sum X Y) : X
    = xy.fst
  dep_snd {X : Set}{Y : X -> Set}(xy : Sum X Y) : Y (dep_fst xy)
    = xy.snd
  dep_cur {X : Set}{Y : X -> Set}{Z : Set}(f : Sum X Y -> Z)
    : (x : X) |-> Y x -> Z
    = \x |-> \y ->  f (dep_pair  x  y)

  dep_uncur {X : Set}{Y : X -> Set}{Z : Set}
    : ((x : X) -> Y x -> Z) -> Sum X Y -> Z
    = \(f : (x : X) -> (x' : Y x) -> Z) -> \(xy : Sum X Y) -> f xy.fst xy.snd
  dep_curry {X : Set}
            {Y : X -> Set}
            (Z : Sum X Y -> Set)
            (f : (xy : Sum X Y) -> Z xy)
    : (x : X) ->  (y : Y x) -> Z (dep_pair x y)
    = \(x : X) -> \(y : Y x) -> f (dep_pair x y)

  dep_uncurry {X : Set}
              {Y : X -> Set}
              (Z : Sum X Y -> Set)
              (f : (x : X) ->
                  (y : Y x) ->
                  Z (dep_pair x y))
              (xy : Sum X Y)
    : Z xy
    = f xy.fst xy.snd
  mapSum {X : Set}{Y1 : X -> Set}{Y2 : X -> Set}(f : (x : X) -> Y1 x -> Y2 x)
    : Sum X Y1 -> Sum X Y2
    = \(p : Sum X Y1) -> dep_pair p.fst (f p.fst p.snd)

  elimSum = dep_uncurry
  ----------------------------------------------------------------------------
  -- Nondependent pairs (binary) cartesian product.
  ----------------------------------------------------------------------------
  Times (X : Set)(Y : Set) : Set
    = Sum X (\(x : X) -> Y)
  pair {X : Set}{Y : Set} : X -> Y -> Times X Y
    = \(x : X) ->
      \(y : Y) ->
      struct {
        fst = x;
        snd = y;}
  fst {X : Set}{Y : Set} : Times X Y -> X
    = \(xy : Times X Y) -> xy.fst
  snd {X : Set}{Y : Set} : Times X Y -> Y
    = \(xy : Times X Y) -> xy.snd
  pairfun {X : Set}{Y : Set}{Z : Set}(f : X -> Y)(g : X -> Z)(x : X)
    : Times Y Z
    = pair (f x) (g x)
  mapTimes {X1 : Set}{X2 : Set}{Y1 : Set}{Y2 : Set}
    : (f : X1 -> X2) -> (g : Y1 -> Y2) -> Times X1 Y1 -> Times X2 Y2
    = \(f : (x : X1) -> X2) ->
      \(g : (x : Y1) -> Y2) ->
      \(xy : Times X1 Y1) ->
      pair (f xy.fst) (g xy.snd)
  swapTimes {X : Set}{Y : Set} : Times X Y -> Times Y X
    = pairfun snd fst
  cur {X : Set}{Y : Set}{Z : Set}(f : Times X Y -> Z) : X -> Y -> Z
    = \(x : X) -> \(y : Y) -> f (pair |_ |_ x y)
  uncur {X : Set}{Y : Set}{Z : Set}(f : X -> Y -> Z) : Times X Y -> Z
    = \(xy : Times X Y) -> f xy.fst xy.snd
  curry {X : Set}
        {Y : Set}
        {Z : Times X Y -> Set}
        (f : (xy : Times X Y) -> Z xy)
    : (x : X) ->
       (y : Y) ->
       Z (pair |_ |_ x y)
    = \(x : X) ->
      \(y : Y) ->
      f (pair |_ |_ x y)

  uncurry {X : Set}
          {Y : Set}
          {Z : Times X Y -> Set}
          (f : (x : X) ->
              (y : Y) ->
              Z (pair |_ |_ x y))
    : (xy : Times X Y) -> Z xy
    = \(xy : Times X Y) -> f xy.fst xy.snd

  elimTimes = uncurry
  ----------------------------------------------------------------------------
  -- Natural numbers.
  ----------------------------------------------------------------------------
  Nat : Set
    = data zer | suc (m : Nat)
  zero : Nat
    = zer@_
  succ (x : Nat) : Nat
    = suc@_ x
  elimNat (C : Nat -> Set)
    : (c_z : C zer@_) ->
       (c_s : (x : Nat) -> C x -> C (suc@_ x)) ->
       (m : Nat) ->
       C m
    = \(c_z : C zer@_) ->
      \(c_s : (x : Nat) -> (x' : C x) -> C (suc@_ x)) ->
      \(m : Nat) ->
      case m of {
        (zer) -> c_z;
        (suc m') -> c_s m' (elimNat C c_z c_s m');}
  ----------------------------------------------------------------------------
  -- Linear universe of finite sets.
  ----------------------------------------------------------------------------
  Fin (m : Nat) : Set
    = case m of {
        (zer) -> Zero;
        (suc m') -> Succ (Fin m');}
  valFin (m : Nat) : Fin m -> Nat
    = \(n : Fin m) ->
      case m of {
        (zer) -> case n of { };
        (suc m') ->
          case n of {
            (zer) -> zer@_;
            (suc n') -> suc@_ (valFin m' n');};}
  zeroFin (m : Nat) : Fin (succ m)
    = zer@_
  succFin (m : Nat)(n : Fin m) : Fin (succ m)
    = suc@_ n
  ----------------------------------------------------------------------------
  -- Do these really belong here?
  ----------------------------------------------------------------------------
  HEAD (X : Set1)(m : Nat)(f : Fin (succ m) -> X) : X
    = f (zeroFin m)
  TAIL (X : Set1)(m : Nat)(f : Fin (succ m) -> X) : Fin m -> X
    = \(n : Fin m) -> f (succFin m n)
  ----------------------------------------------------------------------------
  -- Lists.
  ----------------------------------------------------------------------------
  List (X : Set) : Set
    = data nil | con (x : X) (xs : List X)
  nil {X : Set} : List X
    = nil@_
  con {X : Set}(x : X)(xs : List X) : List X
    = con@_ x xs
  elimList {X : Set}
           (C : List X -> Set)
           (c_nil : C (nil |_))
           (c_con : (x : X) -> (xs : List X) -> C xs -> C (con@_ x xs))
           (xs : List X)
    : C xs
    = case xs of {
        (nil) -> c_nil;
        (con x xs') -> c_con x xs' (elimList |_ C c_nil c_con xs');}
  ----------------------------------------------------------------------------
  -- Tuples are "dependently typed vectors".
  ----------------------------------------------------------------------------
  Nil : Set
    = data nil
  Con (X0 : Set)(X' : Set) : Set
    = data con (x : X0) (xs : X')
  Tuple (m : Nat)(X : Fin m -> Set) : Set
    = case m of {
        (zer) -> Nil;
        (suc m') -> Con (X zer@_) (Tuple m' (\(n : Fin m') -> X (suc@_ n)));}
  ----------------------------------------------------------------------------
  -- Vectors homogeneously typed tuples.
  ----------------------------------------------------------------------------
  Vec (X : Set)(m : Nat) : Set
    = Tuple m (\(n : Fin m) -> X)
  ----------------------------------------------------------------------------
  -- Monoidal expressions.
  ----------------------------------------------------------------------------
  Mon (X : Set) : Set
    = data unit | at (x : X) | mul (xs1 : Mon X) (xs2 : Mon X)
  ----------------------------------------------------------------------------
  -- Propositions.
  ----------------------------------------------------------------------------
  Imply (X : Set)(Y : Set) : Set
    = X -> Y
-}
  Absurd : Set
  Absurd = Zero
  Taut : Set
  Taut = Unit
{-
  Not (X : Set) : Set
    = X -> Absurd
  Exist {X : Set}(P : X -> Set) : Set
    = Sum X P
  Forall (X : Set)(P : X -> Set) : Set
    = (x : X) -> P x
  And (X : Set)(Y : Set) : Set
    = Times X Y
  Iff (X : Set)(Y : Set) : Set
    = And (Imply X Y) (Imply Y X)
  Or (X : Set)(Y : Set) : Set
    = Plus X Y
  Decidable (X : Set) : Set
    = Or X (Imply X Absurd)
  DecidablePred {X : Set}(P : X -> Set) : Set
    = (x : X) -> Decidable (P x)
  DecidableRel {X : Set}(R : X -> X -> Set) : Set
    = (x1 : X) -> (x2 : X) -> Decidable (R x1 x2)
  Least {X : Set}((<=) : X -> X -> Set)(P : X -> Set) : X -> Set
    = \(x : X) -> And (P x) ((x' : X) -> P x' -> (x <= x'))
  Greatest {X : Set}((<=) : X -> X -> Set)(P : X -> Set) : X -> Set
    = \(x : X) -> And (P x) ((x' : X) -> P x' -> (x' <= x))
  ----------------------------------------------------------------------------
  -- Booleans.
  ----------------------------------------------------------------------------
-}
  data Bool : Set where
    true  : Bool
    false : Bool
{-
  elimBool (C : Bool -> Set)(c_t : C true@_)(c_f : C false@_)(p : Bool)
    : C p
    = case p of {
        (true) -> c_t;
        (false) -> c_f;}
  whenBool (C : Set)(c_t : C)(c_f : C) : Bool -> C
    = elimBool (\(x : Bool) -> C) c_t c_f
  pred (X : Set) : Set
    = X -> Bool
-}
--  rel (X : Set) : Set
--    = X -> X -> Bool
  True : Bool -> Set
  True (true)  = Taut
  True (false) = Absurd
{-
  bool2set = True
  pred2Pred {X : Set} : pred X -> X -> Set
    = \(p : pred X) -> \(x : X) -> True (p x)
  rel2Rel {X : Set} : (X -> X -> Bool) -> X -> X -> Set
    = \(r : (X -> X -> Bool)) -> \(x : X) -> \(y : X) -> True (r x y)
  decTrue (p : Bool) : Decidable (True p)
    = case p of {
        (true) -> inl@_ tt;
        (false) -> inr@_ (id |_);}
  abstract dec_lem {P : Set}(decP : Decidable P)
    : Exist |_ (\(b : Bool) -> Iff (True b) P)
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
  dec2bool : (P : Set) |-> (decP : Decidable P) -> Bool
    = \(P : Set) |-> \(decP : Decidable P) -> (dec_lem |_ decP).fst
  dec2bool_spec {P : Set}(decP : Decidable P)
    : Iff (True (dec2bool |_ decP)) P
    = (dec_lem |_ decP).snd

  abstract collTrue : (b : Bool) -> Collapsed (True b)
    = let aux (X : Set)(C : X -> Set)
            : (b : Bool) ->
               (f : True b -> X) ->
               (t1 : True b) |->
               (t2 : True b) |->
               C (f t1) -> C (f t2)
            = \(b : Bool) ->
              case b of {
                (true) ->
                  \(f : (x : True true@_) -> X) ->
                  \(t1 t2 : True true@_) |->
                  \(c : C (f t1)) ->
                  case t1 of { (tt) -> case t2 of { (tt) -> c;};};
                (false) ->
                  \(f : (x : True false@_) -> X) ->
                  \(t1 t2 : True false@_) |->
                  \(c : C (f t1)) ->
                  case t1 of { };}
      in   \(b : Bool) ->  \(P : True b -> Set) -> aux (True b) P b id

  bool2nat (p : Bool) : Nat
    = case p of {
        (true) -> succ zero;
        (false) -> zero;}
  ----------------------------------------------------------------------------
  -- Decidable subsets.
  ----------------------------------------------------------------------------
  Filter {X : Set}(p : pred X) : Set
    = Sum X (pred2Pred |_ p)
  ----------------------------------------------------------------------------
  -- Equality.
  ----------------------------------------------------------------------------
  -- "Deq" stands for "datoid equality" and represents exactly the data
  --  that has to be added to turn a set into a datoid.
  Deq (X : Set) : Set1
    = sig{eq : X -> X -> Bool;
          ref : (x : X) -> True (eq x x);
          subst :
            (C : X -> Set) -> (x1 x2 : X)|-> True (eq x1 x2) -> C x1 -> C x2;}
  -- The "Equality" type represents the data that has to be added to turna
  -- set into a setoid.
  Equality (X : Set) : Set1
    = sig{Equal : X -> X -> Set;
          ref  : Reflexive |_ Equal;
          sym  : Symmetrical |_ Equal;
          tran : Transitive |_ Equal;}
  -}
  data Datoid  : Set1 where
    datoid : (Elem : Set) ->
             (eq : Elem -> Elem -> Bool) ->
             (ref :  (x : Elem) -> True (eq x x)) ->
             (subst : Substitutive  (\x1 -> \x2 -> True (eq x1 x2))) ->
             Datoid

  pElem : Datoid -> Set
  pElem (datoid Elem _ _ _) = Elem


  {-
  ElD (X : Datoid) : Set
    = X.Elem
  eqD {X : Datoid} : ElD X -> ElD X -> Bool
    = X.eq
  EqD {X : Datoid}(x1 x2 : ElD X) : Set
    = True (X.eq x1 x2)

  Setoid : Set1
    = sig{Elem : Set;
          Equal : Elem -> Elem -> Set;
          ref : (x : Elem) -> Equal x x;
          sym : (x1 : Elem) |-> (x2 : Elem) |-> Equal x1 x2 -> Equal x2 x1;
          tran :
            (x1 : Elem) |->
            (x2 : Elem) |->
            (x3 : Elem) |->
            Equal x1 x2 -> Equal x2 x3 -> Equal x1 x3;}
  El (X : Setoid) : Set
    = X.Elem
  Eq {X : Setoid} : Rel (El X)
    = X.Equal

  NotEq {X : Setoid} : Rel (El X)
    = \x1-> \x2-> Not (Eq |X x1 x2)
  Respectable {X : Setoid}(P : El X -> Set) : Set
    = (x1 x2 : El X) |-> Eq |X x1 x2 -> P x1 -> P x2
  RspEq {X Y : Setoid}(f : El X -> El Y) : Set
    = (x1 x2 : El X)  |-> Eq |X x1 x2 -> Eq |Y (f x1) (f x2)
  RspEq2 (|X |Y |Z : Setoid)(f : El X -> El Y -> El Z)
    : Set
    = (x1 x2 :  X.Elem) |-> (y1 y2 :  Y.Elem) ->
      Eq |X x1 x2 ->
      Eq |Y y1 y2  ->
      Eq |Z (f x1 y1) (f x2 y2)
  D2S (Y : Datoid) : Setoid
    = struct {
        Elem = Y.Elem;
        Equal = \(x1 x2 : Elem) -> True (Y.eq x1 x2);
        ref = Y.ref;
        sym =
          \(x1 x2 : Elem) |->
          \(u : Equal x1 x2) ->
          Y.subst (\(x : Y.Elem) -> Equal x x1) |_ |_ u (ref x1);
        tran =
          \(x1 x2 x3 : Elem) |->
          \(u : Equal x1 x2) ->
          \(v : Equal x2 x3) ->
          Y.subst (Equal x1) |_ |_  v u;}

{-# Alfa unfoldgoals off
brief on
hidetypeannots off
wide
nd
hiding on
con "nil" as "[]" with symbolfont
con "con" infix as " : " with symbolfont
var "Forall" as "\"" with symbolfont
var "Exist" as "$" with symbolfont
var "And" infix as "&" with symbolfont
var "Or" infix as "Ú" with symbolfont
var "Iff" infix as "«" with symbolfont
var "Not" as "Ø" with symbolfont
var "Imply" infix as "É" with symbolfont
var "Taut" as "T" with symbolfont
var "Absurd" as "^" with symbolfont
var "El" mixfix as "|_|" with symbolfont
var "Eq" distfix3 as "==" with symbolfont
var "NotEq" distfix3 as "=|=" with symbolfont
var "True" mixfix as "|_|" with symbolfont
var "ElD" mixfix as "|_|" with symbolfont
var "EqD" distfix3 as "==" with symbolfont
var "Id" distfix3 as "=" with symbolfont
 #-}
-}
