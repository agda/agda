
module UnicodeEllipsis where

f : {A B : Set} → (A → B) → A → B
f g a with g a
… | x = x
