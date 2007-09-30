
open import Proc

module Hear (param : Param) where

open import Basics
private open module P = Process param

open Tran

hear : {a : U}{p : Proc a} -> Guard p -> LT a -> Proc a
hear {p = p} g    ⊥        = p
hear og           (lift v) = o
hear (w !g p)     (lift v) = w ! p
hear (>g f)       (lift v) = f v
hear (_ ! _ +g f) (lift v) = f v
hear (g₁ ||g g₂)  (lift v) = hear g₁ (lift v) || hear g₂ (lift v)
hear (φ /|g g)    (lift v) = φ /| hear g (downV φ v)
hear (defg x g)   (lift v) = hear g (lift v)

sound : {a : U}{p : Proc a}(g : Guard p){w : LT a} ->
        p -[ w ]⟶ hear g w
sound g            {⊥}      = qtau
sound og           {lift v} = rx-o
sound (>g _)       {lift v} = rx->
sound (w !g p)     {lift v} = rx-!
sound (w ! p +g f) {lift v} = rx-+
sound (g₁ ||g g₂)  {lift v} = rx-|| (sound g₁) (sound g₂)
sound (φ /|g g)    {lift v} = rx-/| (sound g)
sound (defg x g)   {lift v} = rx-def (sound g)

uniq : {a : U}{p : Proc a}{w : LT a}{px py : Proc a} -> 
       p -[ w ]⟶ px -> p -[ w ]⟶ py -> px == py
uniq qtau qtau = refl
uniq rx-o rx-o = refl
uniq rx-> rx-> = refl
uniq rx-! rx-! = refl
uniq rx-+ rx-+ = refl
uniq (rx-|| l₁ r₁) (rx-|| l₂ r₂) with uniq l₁ l₂ | uniq r₁ r₂
... | refl | refl = refl
uniq (rx-/| r₁) (rx-/| r₂) with uniq r₁ r₂
... | refl = refl
uniq (rx-def r₁) (rx-def r₂) with uniq r₁ r₂
... | refl = refl

complete : {a : U}{p : Proc a}(g : Guard p){w : LT a}{p' : Proc a} ->
           p -[ w ]⟶ p' -> p' == hear g w
complete g r = uniq r (sound g)
