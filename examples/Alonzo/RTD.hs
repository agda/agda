{-# OPTIONS -fglasgow-exts -cpp #-}
module RTD(cast, Typeable(..), mkTyCon, mkTyConApp,
 Dynamic ) where
import GHC.Base
import Data.Typeable(Typeable(..), mkTyCon, mkTyConApp)
import Data.Dynamic(Dynamic)

cast :: a -> b 
cast = unsafeCoerce#

