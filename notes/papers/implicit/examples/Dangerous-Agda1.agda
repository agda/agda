
data N : Set = zero | suc (n:N)
data B : Set = true | false

data False : Set =
data True  : Set = tt

F : B -> Set
F true  = N
F false = B

G : (x:B) -> F x -> Set
G false _      = N
G true zero    = B
G true (suc n) = N

(==) : B -> B -> Set
true == true = True
false == false = True
_ == _ = False

data Equal (x,y:B) : Set where
  equal : x == y -> Equal x y

refl : (x:B) -> Equal x x
refl true = equal tt
refl false = equal tt

postulate
  f : (x:B) -> (y : F x) -> G x y -> N -- Equal x true -> N

h : N
h = f _ false zero --(refl true)

