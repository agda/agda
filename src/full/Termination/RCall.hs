module Termination.RCall where

import Syntax.Internal as I
import Syntax.Abstract.Name
import Syntax.Abstract.Pretty
import Syntax.Common
import qualified Syntax.Concrete as C
import Syntax.Position(noRange)
import Syntax.Scope.Base
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
   callFun :: QName,
   callClause :: Int,
   callNumber :: Int,
   callArgs :: Args
} 


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

