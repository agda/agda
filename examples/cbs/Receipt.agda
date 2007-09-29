
open import Proc

module Receipt (param : Param) where

import Interp
open import Basics

private open module P = Process param
private open module I = Interp param

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
