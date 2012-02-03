
module Issue552 where

data Id3 {A : Set} : A -> A -> A -> Set where
  refl3 : {x : A} -> Id3 x x x

-- These work:

ok1 : {A : Set}(a b c : A) -> Id3 a b c -> Id3 a b c
ok1 ._ ._ ._ (refl3 {_}) = refl3

ok2 : {A : Set}(a b c : A) -> Id3 a b c -> Id3 a b c
ok2 _ ._ ._ (refl3) = refl3

ok3 : {A : Set}(a b c : A) -> Id3 a b c -> Id3 a b c
ok3 _ ._ ._ (refl3 {._}) = refl3

-- These work after the fix:

bad4 : {A : Set}(a b c : A) -> Id3 a b c -> Id3 a b c
bad4 ._ ._ _ (refl3 {._}) = refl3

bad3 : {A : Set}(a b c : A) -> Id3 a b c -> Id3 a b c
bad3 ._ _ ._ (refl3 {._}) = refl3

-- This still doesn't work:

-- bad1 : {A : Set}(a b c : A) -> Id3 a b c -> Id3 a b c
-- bad1 ._ ._ ._ (refl3) = refl3
