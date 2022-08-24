{-# OPTIONS --guardedness #-}

module type-synonym-args where

postulate
  Functor : (Set → Set) → Set
  fmap    : ∀{F A B} ⦃ _ : Functor F ⦄ → (A → B) → F A → F B

{-# FOREIGN GHC data FunctorDict f = Functor f => FunctorDict    #-}
{-# COMPILE GHC Functor            = type(0) FunctorDict         #-} -- compiles to `type T_Functor_2 = Functor`
{-# COMPILE GHC fmap               = \ f a b FunctorDict -> fmap #-}

--------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.List using (List; _∷_; [])

postulate
  Identity           : Set → Set
  mkIdentity         : ∀{A} → A → Identity A
  runIdentity        : ∀{A} → Identity A → A
  instance
    Identity-functor : Functor Identity -- `Identity` used without args, errors when it is defined eta expanded

{-# FOREIGN GHC import Data.Functor.Identity (Identity(Identity), runIdentity) #-}

{-# COMPILE GHC Identity         = type(0) Identity   #-} -- compiles to `type T_Identity_14 = Identity`
{-# COMPILE GHC mkIdentity       = \ a -> Identity    #-}
{-# COMPILE GHC runIdentity      = \ a -> runIdentity #-}
{-# COMPILE GHC Identity-functor = FunctorDict        #-}

test : Identity Bool
test = fmap
  (λ { false → true
     ; true  → false
     })
  (mkIdentity true)

open import IO using (IO)
open import Data.Bool.Show using (show)
open import Data.String.Base using (_++_)

main : IO.Main
main = IO.run (IO.putStrLn ("false = " ++ show (runIdentity test)))

--------

postulate
  X : Set → Set

{-# FOREIGN GHC type HsSynonym a = a  #-}

-- Equivalent
{-# COMPILE GHC X = type(1) HsSynonym #-} 
-- {-# COMPILE GHC X = type HsSynonym #-}

-- Error (HsSynonym not applied to enough arguments)
-- {-# COMPILE GHC X = type(0) HsSynonym #-}
