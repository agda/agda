
module Span where

open import Prelude
open import Star
open import Modal

data SpanView {A : Set}{R : Rel A}(p : {a b : A} -> R a b -> Bool) :
              EdgePred (Star R) where
  oneFalse : {a b c d : A}(xs : Star R a b)(pxs : All (\x -> IsTrue (p x)) xs)
             (x : R b c)(¬px : IsFalse (p x))(ys : Star R c d) ->
             SpanView p (xs ++ x • ys)
  allTrue  : {a b : A}{xs : Star R a b}(ts : All (\x -> IsTrue (p x)) xs) ->
             SpanView p xs

span : {A : Set}{R : Rel A}(p : {a b : A} -> R a b -> Bool){a b : A}
       (xs : Star R a b) -> SpanView p xs
span p ε = allTrue ε
span p (x • xs) with inspect (p x)
span p (x • xs) | itsFalse ¬px = oneFalse ε ε x ¬px xs
span p (x • xs) | itsTrue px with span p xs
span p (x • .(xs ++ y • ys)) | itsTrue px
     | oneFalse xs pxs y ¬py ys =
       oneFalse (x • xs) (check px • pxs) y ¬py ys
span p (x • xs) | itsTrue px | allTrue pxs =
       allTrue (check px • pxs)

_│_ : {A : Set}(R : Rel A)(P : EdgePred R) -> Rel A
(R │ P) a b = Σ (R a b) P

forget : {A : Set}{R : Rel A}{P : EdgePred R} -> Star (R │ P) =[ id ]=> Star R
forget = map id fst

data SpanView' {A : Set}{R : Rel A}(p : {a b : A} -> R a b -> Bool) :
               EdgePred (Star R) where
  oneFalse' : {a b c d : A}(xs : Star (R │ \{a b} x -> IsTrue (p x)) a b)
              (x : R b c)(¬px : IsFalse (p x))(ys : Star R c d) ->
              SpanView' p (forget xs ++ x • ys)
  allTrue'  : {a b : A}(xs : Star (R │ \{a b} x -> IsTrue (p x)) a b) ->
              SpanView' p (forget xs)

span' : {A : Set}{R : Rel A}(p : {a b : A} -> R a b -> Bool){a b : A}
        (xs : Star R a b) -> SpanView' p xs
span' p ε = allTrue' ε
span' p (x • xs) with inspect (p x)
span' p (x • xs) | itsFalse ¬px = oneFalse' ε x ¬px xs
span' p (x • xs) | itsTrue px with span' p xs
span' p (x • .(forget xs ++ y • ys)) | itsTrue px
        | oneFalse' xs y ¬py ys = oneFalse' ((x ,, px) • xs) y ¬py ys
span' p (x • .(forget xs)) | itsTrue px
        | allTrue' xs = allTrue' ((x ,, px) • xs)

-- Can't seem to define it as 'map Some.a (\x -> (_ ,, uncheck x))'
all│ : {A : Set}{R : Rel A}{P : EdgePred R}{a b : A}{xs : Star R a b} ->
       All P xs -> Star (R │ P) a b
all│ (check p • pxs) = (_ ,, p) • all│ pxs
all│ ε               = ε
