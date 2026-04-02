{-# OPTIONS --erasure --no-load-primitives
            --no-erased-levels-in-primitives #-}

{-# BUILTIN PROP           Prop      #-}
{-# BUILTIN PROPOMEGA      Propω     #-}
{-# BUILTIN TYPE           Set       #-}
{-# BUILTIN SETOMEGA       Setω      #-}
{-# BUILTIN STRICTSET      SSet      #-}
{-# BUILTIN STRICTSETOMEGA SSetω     #-}
{-# BUILTIN LEVELUNIV      LevelUniv #-}

postulate
  Level : LevelUniv
  lzero : Level
  lsuc  : Level → Level
  _⊔_   : (_ _ : Level) → Level

{-# BUILTIN LEVEL     Level #-}
{-# BUILTIN LEVELZERO lzero #-}
{-# BUILTIN LEVELSUC  lsuc  #-}
{-# BUILTIN LEVELMAX  _⊔_   #-}

data _≡_ {a} {A : Set a} (x : A) : A → Set a where
  refl : x ≡ x

{-# BUILTIN EQUALITY _≡_ #-}

primitive
  primEraseEquality : ∀ {@0 a} {A : Set a} {x y : A} → x ≡ y → x ≡ y
