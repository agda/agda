\nonstopmode
\documentclass{article}

\usepackage{agda}

\begin{document}
\begin{code}

{-# OPTIONS --copatterns --sized-types #-}

{-# BUILTIN SIZE    Size   #-}
{-# BUILTIN SIZELT  Size<_ #-}
{-# BUILTIN SIZESUC ↑_     #-}
{-# BUILTIN SIZEINF ∞      #-}

data List (A : Set) : Set where
  [] : List A
  _∷_ : (x : A) (xs : List A) -> List A

record _×_ (A B : Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B
open _×_

-- Sized streams via head/tail.

record Stream {i : Size} (A : Set) : Set where
  coinductive; constructor _∷_
  field
    head  : A
    tail  : ∀ {j : Size< i} → Stream {j} A
open Stream public

_∷ˢ_ : ∀ {i A} → A → Stream {i} A → Stream {↑ i} A
head  (a ∷ˢ as) = a
tail  (a ∷ˢ as) = as

-- Streams and lists.

-- Prepending a list to a stream.

_++ˢ_ : ∀ {i A} → List A → Stream {i} A → Stream {i} A
[]        ++ˢ s = s
(a ∷ as)  ++ˢ s = a ∷ˢ (as ++ˢ s)

-- Unfold which produces several outputs at one step

record List1 (A : Set) : Set where
  constructor _∷_
  field
    head  : A
    tail  : List A
open List1 using (head; tail)

record ⊤ : Set where constructor trivial
open List1 (trivial ∷ []) using (head; tail) -- problem: imports not colored

unfold⁺ : ∀ {S : Size → Set} {A : Set}

  (step : ∀ {i} → S i → List1 A × (∀ {j : Size< i} → S j)) →

  ∀ {i} → (s : S i) → Stream {i} A

head  (unfold⁺ step s) =  head (fst (step s))
tail  (unfold⁺ step s) =  let  ((_ ∷ l) , s′) = step s
                          in   l ++ˢ unfold⁺ step s′
\end{code}
Problem: The ∷ in the last let statement is not colored with constructor color.
\end{document}
