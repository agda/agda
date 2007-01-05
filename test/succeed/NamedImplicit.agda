
module NamedImplicit where

postulate
  T    : Set -> Set
  map' : (A B : Set) -> (A -> B) -> T A -> T B

map : {A B : Set} -> (A -> B) -> T A -> T B
map = map' _ _

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

data Bool : Set where
  true  : Bool
  false : Bool

id : {A : Set} -> A -> A
id x = x

const : {A B : Set} -> A -> B -> A
const x y = x

postulate
  unsafeCoerce : {A B : Set} -> A -> B

test1 = map {B = Nat} id
test2 = map {A = Nat} (const zero)
test3 = map {B = Bool} (unsafeCoerce {A = Nat})
test4 = map {B = Nat -> Nat} (const {B = Bool} id)


f : {A B C D : Set} -> D -> D
f {D = X} = \(x : X) -> x

