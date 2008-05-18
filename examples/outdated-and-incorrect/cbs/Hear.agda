
open import Proc

module Hear (param : Param) where

open import Basics
private open module P = Process param

open Tran

hear : {a : U}{p : Proc a} -> Guard p -> LT a -> Proc a
hear {p = p} g    bot      = p
hear og           (lift v) = o
hear (w !g p)     (lift v) = w ! p
hear (>g f)       (lift v) = f v
hear (_ ! _ +g f) (lift v) = f v
hear (g1 ||g g2)  (lift v) = hear g1 (lift v) || hear g2 (lift v)
hear (φ /|g g)    (lift v) = φ /| hear g (downV φ v)
hear (defg x g)   (lift v) = hear g (lift v)

sound : {a : U}{p : Proc a}(g : Guard p){w : LT a} ->
        p -[ w ]-> hear g w
sound g            {bot}    = qtau
sound og           {lift v} = rx-o
sound (>g _)       {lift v} = rx->
sound (w !g p)     {lift v} = rx-!
sound (w ! p +g f) {lift v} = rx-+
sound (g1 ||g g2)  {lift v} = rx-|| (sound g1) (sound g2)
sound (φ /|g g)    {lift v} = rx-/| (sound g)
sound (defg x g)   {lift v} = rx-def (sound g)

uniq : {a : U}{p : Proc a}{w : LT a}{px py : Proc a} -> 
       p -[ w ]-> px -> p -[ w ]-> py -> px == py
uniq qtau qtau = refl
uniq rx-o rx-o = refl
uniq rx-> rx-> = refl
uniq rx-! rx-! = refl
uniq rx-+ rx-+ = refl
uniq (rx-|| l1 r1) (rx-|| l2 r2) with uniq l1 l2 | uniq r1 r2
... | refl | refl = refl
uniq (rx-/| r1) (rx-/| r2) with uniq r1 r2
... | refl = refl
uniq (rx-def r1) (rx-def r2) with uniq r1 r2
... | refl = refl

complete : {a : U}{p : Proc a}(g : Guard p){w : LT a}{p' : Proc a} ->
           p -[ w ]-> p' -> p' == hear g w
complete g r = uniq r (sound g)
