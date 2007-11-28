{-# OPTIONS --no-positivity-check #-}

module Generics where

data Zero : Set where
data One  : Set where
  ∙ : One

data _+_ (A B : Set) : Set where
  inl : A -> A + B
  inr : B -> A + B

data _×_ (A : Set)(B : A -> Set) : Set where
  <_,_> : (x : A) -> B x -> A × B

data _==_ {A : Set}(x : A) : A -> Set where
  refl : x == x

data Shape (I : Set) : Set where
  ι : Shape I
  σ : Shape I -> Shape I
  δ : Shape I -> Shape I

data Tel {I : Set} : Shape I -> Set1 where
  empty	  : Tel ι
  non-rec : {s : Shape I}(A : Set) -> (A -> Tel s) -> Tel (σ s)
  rec	  : {s : Shape I}(H : Set) -> (H -> I) -> Tel s -> Tel (δ s)

Index : {I : Set}(E : Set){s : Shape I} -> Tel s -> Set
Index E  empty	      = E
Index E (non-rec A f) = (x : A) -> Index E (f x)
Index E (rec H i s)   = Index E s

data Con (I E : Set) : Set1 where
  con : {s : Shape I}(tel : Tel s) -> Index E tel -> Con I E

infixr 40 _|_

data OP (I E : Set) : Set1 where
  ∅   : OP I E
  _|_ : Con I E -> OP I E -> OP I E

Args-tel : {I : Set}(U : I -> Set){s : Shape I} -> Tel s -> Set
Args-tel U empty	 = One
Args-tel U (non-rec A s) = A × \a -> Args-tel U (s a)
Args-tel U (rec H i s)   = ((x : H) -> U (i x)) × \_ -> Args-tel U s

Args : {I E : Set}(U : I -> Set) -> OP I E -> Set
Args U ∅	       = Zero
Args U (con tel _ | γ) = Args-tel U tel + Args U γ

index-tel : {I E : Set}{s : Shape I}(U : I -> Set)(tel : Tel s) -> Index E tel -> Args-tel U tel -> E
index-tel U  empty	  i ∙		= i
index-tel U (non-rec A s) i < a , arg > = index-tel U (s a) (i a) arg
index-tel U (rec H di s)  i < d , arg > = index-tel U s i arg

index : {I E : Set}(U : I -> Set)(γ : OP I E) -> Args U γ -> E
index U ∅		()
index U (con tel i | _) (inl x) = index-tel U tel i x
index U (con _ _   | γ) (inr y) = index U γ y

OPr : Set -> Set1
OPr I = I -> OP I One

data Ur {I : Set}(γ : OPr I)(i : I) : Set where
  intror : Args (Ur γ) (γ i) -> Ur γ i

OPg : Set -> Set1
OPg I = OP I I

const-index : {I E : Set}{s : Shape I} -> E -> (tel : Tel s) -> Index E tel
const-index i  empty	   = i
const-index i (non-rec _ s)   = \a -> const-index i (s a)
const-index i (rec _ _ s) = const-index i s

ε-shape : {I : Set} -> Shape I -> Shape I
ε-shape  ι    = σ ι
ε-shape (σ s) = σ (ε-shape s)
ε-shape (δ s) = δ (ε-shape s)

ε-tel : {I : Set}{s : Shape I} -> I -> (tel : Tel s) -> Index I tel -> Tel (ε-shape s)
ε-tel i  empty		j = non-rec (j == i) \_ -> empty
ε-tel i (non-rec A arg) j = non-rec A \a -> ε-tel i (arg a) (j a)
ε-tel i (rec H di arg)  j = rec H di (ε-tel i arg j)

ε-con : {I : Set} -> I -> Con I I -> Con I One
ε-con j (con tel i) = con args' (const-index ∙ args')
  where
    args' = ε-tel j tel i

ε : {I : Set} -> OPg I -> OPr I
ε  ∅	  _ = ∅
ε (c | γ) j = ε-con j c | ε γ j

Ug : {I : Set} -> OPg I -> I -> Set
Ug γ = Ur (ε γ)

g→rArgs-tel : {I : Set}(U : I -> Set){s : Shape I}
	      (tel : Tel s)(i : Index I tel)(arg : Args-tel U tel) ->
	      Args-tel U (ε-tel (index-tel U tel i arg) tel i)
g→rArgs-tel U  empty	      i ∙	    = < refl , ∙ >
g→rArgs-tel U (non-rec A tel) i < a , arg > = < a , g→rArgs-tel U (tel a) (i a) arg >
g→rArgs-tel U (rec H di tel)  i < d , arg > = < d , g→rArgs-tel U tel i arg >

g→rArgs : {I : Set}(U : I -> Set)(γ : OPg I)(a : Args U γ) -> Args U (ε γ (index U γ a))
g→rArgs U ∅		  ()
g→rArgs U (con tel i | _) (inl arg) = inl (g→rArgs-tel U tel i arg)
g→rArgs U (con _   _ | γ) (inr arg) = inr (g→rArgs U γ arg)

introg : {I : Set}(γ : OPg I)(a : Args (Ug γ) γ) -> Ug γ (index (Ug γ) γ a)
introg γ a = intror (g→rArgs (Ug γ) γ a)

r→gArgs-tel : {I : Set}(U : I -> Set){s : Shape I}(tel : Tel s)(ind : Index I tel)
	      (i : I) -> Args-tel U (ε-tel i tel ind) -> Args-tel U tel
r→gArgs-tel U  empty	      ind i < p , ∙ >	= ∙
r→gArgs-tel U (non-rec A tel) ind i < a , arg > = < a , r→gArgs-tel U (tel a) (ind a) i arg >
r→gArgs-tel U (rec H di tel)  ind i < d , arg > = < d , r→gArgs-tel U tel ind i arg >

r→gArgs : {I : Set}(U : I -> Set)(γ : OPg I)(i : I)(a : Args U (ε γ i)) -> Args U γ
r→gArgs U  ∅		  _ ()
r→gArgs U (con tel ind | _) i (inl arg) = inl (r→gArgs-tel U tel ind i arg)
r→gArgs U (con _   _   | γ) i (inr arg) = inr (r→gArgs U γ i arg)

-- Elimination rules

IndArg-tel : {I : Set}(U : I -> Set){s : Shape I}(tel : Tel s) -> Args-tel U tel -> Set
IndArg-tel U  empty	     ∙		 = Zero
IndArg-tel U (non-rec A tel) < a , arg > = IndArg-tel U (tel a) arg
IndArg-tel U (rec H di tel)  < d , arg > = H + IndArg-tel U tel arg

IndArg : {I E : Set}(U : I -> Set)(γ : OP I E) -> Args U γ -> Set
IndArg U  ∅		 ()
IndArg U (con tel _ | _) (inl arg) = IndArg-tel U tel arg
IndArg U (con _   _ | γ) (inr arg) = IndArg U γ arg

-- Examples

nat : OPr One
nat = \i -> con empty ∙ | con (rec One (\_ -> ∙) empty) ∙ | ∅

N : Set
N = Ur nat ∙

z : N
z = intror (inl ∙)

s : N -> N
s n = intror (inr (inl < (\_ -> n) , ∙ >))

