module IORef where

  data Unit : Set where
    unit : Unit

  data Pair (A B : Set) : Set where
    pair : A -> B -> Pair A B

  fst : {A B : Set} -> Pair A B -> A
  fst (pair a b) = a

  snd : {A B : Set} -> Pair A B -> B
  snd (pair a b) = b

  data Nat : Set where
    zero : Nat
    suc : Nat -> Nat

  data Fin : Nat -> Set where
    fz : {n : Nat} -> Fin (suc n)
    fs : {n : Nat} -> Fin n -> Fin (suc n) 

  infixr 40 _::_
  infixl 20 _!_

  data Vec (A : Set) : Nat -> Set where
    []   : Vec A zero
    _::_ : {n : Nat} -> A -> Vec A n -> Vec A (suc n)

  _!_ : {A : Set}{n : Nat} -> Vec A n -> Fin n -> A
  []	  ! ()
  x :: _  ! fz	   = x
  _ :: xs ! (fs i) = xs ! i

  Loc : Nat -> Set
  Loc = Fin


  -- A universe. IORefs can store data of type el(u), for some u : U
  postulate
    U : Set
    el : U -> Set

  -- Shapes tell you what types live on the heap.
  Shape : Nat -> Set
  Shape n = Vec U n -- Fin n -> U

  -- Shapes can grow as you allocate new memory  
  _||_ : {n : Nat} -> Shape n -> U -> Shape (suc n)
  xs || u = u :: xs

  infixl 40 _▻_
  infixl 60 _[_:=_] _[_]

  -- The heap maps locations to elements of the right type.
  data Heap : {n : Nat}(s : Shape n) -> Set where
    ε	: Heap []
    _▻_ : {n : Nat}{s : Shape n}{a : U} -> Heap s -> el a -> Heap (s || a)

--   Heap : {n : Nat} -> Shape n -> Set 
--   Heap {n} shape = (k : Fin n) -> el (shape ! k)

  _[_:=_] : {n : Nat}{s : Shape n} -> Heap s -> (l : Loc n) -> el (s ! l) -> Heap s
  ε	  [ ()   := _ ]
  (h ▻ _) [ fz   := x ] = h ▻ x
  (h ▻ y) [ fs i := x ] = h [ i := x ] ▻ y

  _[_] : {n : Nat}{s : Shape n} -> Heap s -> (l : Loc n) -> el (s ! l)
  ε	  [ ()	 ]
  (h ▻ x) [ fz	 ] = x
  (h ▻ _) [ fs i ] = h [ i ]

--   (h [ fz := x ]) fz = x
--   (h [ fz := x ]) (fs i) = h (fs i)
--   (h [ fs i := x ]) fz = h fz
--   _[_:=_] {._}{_ :: s} h (fs i) x (fs j) = _[_:=_] {s = s} (\z -> h (fs z)) i x j

  -- Well-scoped, well-typed IORefs
  data IO (A : Set) : {n m : Nat} -> Shape n -> Shape m -> Set where
    Return : {n : Nat}{s : Shape n} -> A -> IO A s s
    WriteIORef : {n m : Nat}{s : Shape n}{t : Shape m} -> 
      (loc : Loc n) -> el (s ! loc) -> IO A s t -> IO A s t
    ReadIORef : {n m : Nat}{s : Shape n}{t : Shape m} ->
      (loc : Loc n) -> (el (s ! loc) -> IO A s t) -> IO A s t
    NewIORef : {n m : Nat}{s : Shape n}{t : Shape m}{u : U} -> 
      el u -> IO A (s || u) t -> IO A s t 

  -- Running IO programs
  run : {A : Set} -> {n m : Nat} -> {s : Shape n} -> {t : Shape m}
       -> Heap s -> IO A s t -> Pair A (Heap t)
  run heap (Return x) = pair x heap
  run heap (WriteIORef l x io) = run (heap [ l := x ]) io
  run heap (ReadIORef l k) = run heap (k (heap [ l ]))
  run heap (NewIORef x k) = run (heap ▻ x) k

  infixr 10 _>>=_ _>>_

  _>>=_ : {A B : Set}{n₁ n₂ n₃ : Nat}{s₁ : Shape n₁}{s₂ : Shape n₂}{s₃ : Shape n₃} ->
	  IO A s₁ s₂ -> (A -> IO B s₂ s₃) -> IO B s₁ s₃
  Return x	   >>= f = f x
  WriteIORef r x k >>= f = WriteIORef r x (k >>= f)
  ReadIORef r k	   >>= f = ReadIORef r (\x -> k x >>= f)
  NewIORef x k	   >>= f = NewIORef x (k >>= f)

  _>>_ : {A B : Set}{n₁ n₂ n₃ : Nat}{s₁ : Shape n₁}{s₂ : Shape n₂}{s₃ : Shape n₃} ->
	 IO A s₁ s₂ -> IO B s₂ s₃ -> IO B s₁ s₃
  a >> b = a >>= \_ -> b

  -- The operations without CPS

  data IORef : {n : Nat}(s : Shape n) -> U -> Set where
    ioRef : {n : Nat}{s : Shape n}(r : Loc n) -> IORef s (s ! r)

  return : {A : Set}{n : Nat}{s : Shape n} -> A -> IO A s s
  return = Return

  writeIORef : {n : Nat}{s : Shape n}{a : U} ->
	       IORef s a -> el a -> IO Unit s s
  writeIORef (ioRef r) x = WriteIORef r x (Return unit)

  readIORef : {n : Nat}{s : Shape n}{a : U} -> IORef s a -> IO (el a) s s
  readIORef (ioRef r) = ReadIORef r Return

  newIORef : {n : Nat}{s : Shape n}{a : U} -> el a -> IO (IORef (s || a) a) s (s || a)
  newIORef x = NewIORef x (Return (ioRef fz))

  -- Some nice properties

  infix 10 _==_ _≡_

  data _==_ {A : Set}(x : A) : A -> Set where
    refl : x == x

  subst : {A : Set}(P : A -> Set){x y : A} -> x == y -> P y -> P x
  subst {A} P refl Px = Px

  cong : {A B : Set}(f : A -> B){x y : A} -> x == y -> f x == f y
  cong {A} f refl = refl

  trans : {A : Set}{x y z : A} -> x == y -> y == z -> x == z
  trans {A} refl p = p

  fsteq : {A B : Set}{x y : A}{z w : B} -> pair x z == pair y w -> x == y
  fsteq {A}{B} refl = refl

  -- Lemmas

  update-lookup : {n : Nat}{s : Shape n}(h : Heap s)(r : Loc n)(x : el (s ! r)) ->
		  h [ r := x ] [ r ] == x
  update-lookup ε	()     _
  update-lookup	(h ▻ _) fz     x = refl
  update-lookup (h ▻ _) (fs i) x = update-lookup h i x

  update-update : {n : Nat}{s : Shape n}(h : Heap s)(r : Loc n)(x y : el (s ! r)) ->
		  h [ r := x ] [ r := y ] == h [ r := y ]
  update-update ε	()     _ _
  update-update (h ▻ _)  fz    x y = refl
  update-update (h ▻ z) (fs i) x y = cong (\ ∙ -> ∙ ▻ z) (update-update h i x y)

  -- Equality of monadic computations

  data _≡_ {A : Set}{n m : Nat}{s : Shape n}{t : Shape m}(io₁ io₂ : IO A s t) : Set where
    eqIO : ((h : Heap s) -> run h io₁ == run h io₂) -> io₁ ≡ io₂

  uneqIO : {A : Set}{n m : Nat}{s : Shape n}{t : Shape m}{io₁ io₂ : IO A s t} ->
	   io₁ ≡ io₂ -> (h : Heap s) -> run h io₁ == run h io₂
  uneqIO (eqIO e) = e

  -- Congruence properties

  cong->> : {A B : Set}{n₁ n₂ n₃ : Nat}{s₁ : Shape n₁}{s₂ : Shape n₂}{s₃ : Shape n₃}
	    {io₁₁ io₁₂ : IO A s₁ s₂}{io₂₁ io₂₂ : A -> IO B s₂ s₃} ->
	    io₁₁ ≡ io₁₂ -> ((x : A) -> io₂₁ x ≡ io₂₂ x) -> io₁₁ >>= io₂₁ ≡ io₁₂ >>= io₂₂
  cong->> {A}{B}{s₁ = s₁}{s₂}{s₃}{io₁₁}{io₁₂}{io₂₁}{io₂₂}(eqIO eq₁) eq₂ =
      eqIO (prf io₁₁ io₁₂ io₂₁ io₂₂ eq₁ eq₂)
    where
      prf : {n₁ n₂ n₃ : Nat}{s₁ : Shape n₁}{s₂ : Shape n₂}{s₃ : Shape n₃}
	    (io₁₁ io₁₂ : IO A s₁ s₂)(io₂₁ io₂₂ : A -> IO B s₂ s₃) ->
	    ((h : Heap s₁) -> run h io₁₁ == run h io₁₂) ->
	    ((x : A) -> io₂₁ x ≡ io₂₂ x) ->
	    (h : Heap s₁) -> run h (io₁₁ >>= io₂₁) == run h (io₁₂ >>= io₂₂)
      prf (Return x) (Return y) k₁ k₂ eq₁ eq₂ h =
	  subst (\ ∙ -> run h (k₁ ∙) == run h (k₂ y)) x=y (uneqIO (eq₂ y) h)
	where
	  x=y : x == y
	  x=y = fsteq (eq₁ h)
      prf (WriteIORef r₁ x₁ k₁) (Return y) k₂ k₃ eq₁ eq₂ h = ?
      -- ... boring proofs

  -- Monad laws

    -- boring...

  -- IO laws

  new-read : {n : Nat}{s : Shape n}{a : U}(x : el a) ->
	     newIORef {s = s} x >>= readIORef ≡
	     newIORef x >> return x
  new-read x = eqIO \h -> refl

  write-read : {n : Nat}{s : Shape n}{a : U}(r : IORef s a)(x : el a) ->
	       writeIORef r x >> readIORef r
	       ≡ writeIORef r x >> return x
  write-read (ioRef r) x =
    eqIO \h -> cong (\ ∙ -> pair ∙ (h [ r := x ]))
		    (update-lookup h r x)

  write-write : {n : Nat}{s : Shape n}{a : U}(r : IORef s a)(x y : el a) ->
		writeIORef r x >> writeIORef r y
		≡ writeIORef r y
  write-write (ioRef r) x y =
    eqIO \h -> cong (\ ∙ -> pair unit ∙) (update-update h r x y)

  -- Some separation properties would be nice

