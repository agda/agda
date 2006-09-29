module Termination.RCall where

import Syntax.Internal as I
import Syntax.Abstract.Name
import Syntax.Abstract.Pretty
import Syntax.Common
import qualified Syntax.Concrete as C
import Syntax.Position(noRange)
import Syntax.Scope
import Syntax.Translation.ConcreteToAbstract
import TypeChecking.Monad
import TypeChecking.Errors

import Termination.Utils

import Utils.Pretty
import Utils.Monad

import Control.Monad.Error
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Trans
import qualified Data.Map as Map
import Data.List as List
import Text.PrettyPrint

data  RCall = RCall {
   callFun :: Name,
   callClause :: Int,
   callNumber :: Int,
   callArgs :: Args
} 


instance Show RCall where
  show r = (show $ callFun r) ++  (show $ callArgs r)

instance PrettyTCM RCall where
  prettyTCM r = do
		  dargs <- prettyTCM  (callArgs r)
		  return $ dr <> dargs 
                where
	dr = pretty $ callFun r
        dargs = text ""

instance PrettyTCM  a => PrettyTCM [a] where
  prettyTCM [] = return $ text ""
  prettyTCM (r:rs) = do 
			dr <- prettyTCM r 
			ds <- prettyTCM rs
                        return $ dr <> comma <> ds
instance PrettyTCM a => PrettyTCM (Arg a) where
  prettyTCM (Arg h x) = prettyTCM x
