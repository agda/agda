{-# OPTIONS --no-pattern-matching #-}

id : {A : Set} (x : A) → A
id x = x

const : {A B : Set} (x : A) (y : B) → A
const x y = x

happ : {A B C : Set} (f : A → B → C) (g : A → B) (x : A) → C
happ f g x = f x (g x)

K = const
S = happ

I : {A : Set} (x : A) → A
I {A} = S K (K {B = A})

-- Mmh, pretty boring...
