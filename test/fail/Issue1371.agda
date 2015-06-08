open import Common.Prelude
open import Common.Reflection
open import Common.Equality

A : Set
a : A
A = _

aName : QName
aName = quote a

B : Set
b : B
B = _

bName : QName
bName = quote b

aName=bName : primQNameType aName ≡ primQNameType bName
aName=bName = refl

a = 0
b = 1.0

empty : ⊥
empty with aName=bName
... | ()
