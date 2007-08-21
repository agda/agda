{-# OPTIONS -fglasgow-exts -cpp #-}
module RTS(cast, Typeable, mkTyCon, mkTyConApp) where
import GHC.Base
import Data.Typeable(Typeable, mkTyCon, mkTyConApp)

cast :: a -> b 
cast = unsafeCoerce#

type Code = ()
