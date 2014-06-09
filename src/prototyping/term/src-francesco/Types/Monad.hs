module Types.Monad
    ( -- * Monad definition
      TC
    , ClosedTC
    , runTC
    , TCState
    , initTCState
    , TCErr(..)
    , TCReport(..)
    , tcReport
      -- * Operations
      -- ** Errors
    , typeError
      -- ** Source location
    , atSrcLoc
      -- ** Getting the 'Signature'
    , getSignature
      -- ** Definition handling
    , addDefinition
    , getDefinition
      -- ** MetaVar handling
    , addMetaVar
    , instantiateMetaVar
    , getTypeOfMetaVar
    , getBodyOfMetaVar
      -- ** Context handling
    , askContext
    , localContext
    , liftClosed
    , extendContext
    , getTypeOfName
    , getTypeOfVar
      -- * Problem handling
    , ProblemId
    , Stuck(..)
    , StuckTC
    , newProblem
    , newProblem_
    , bindProblem
    , waitOnProblem
    , solveProblems
    ) where

import Prelude                                    hiding (abs, pi)

import qualified Data.Set                         as Set
import           Data.Typeable                    (Typeable)

import qualified Text.PrettyPrint.Extended        as PP
import           Syntax.Abstract                  (Name)
import           Syntax.Abstract.Pretty           ()
import           Types.Definition
import           Types.Var
import           Types.Term
import qualified Types.Context                    as Ctx
import           Types.Monad.Base
import qualified Types.Signature                  as Sig

-- Utilities
------------------------------------------------------------------------

modifySignature :: (Sig.Signature t -> Sig.Signature t) -> TC t v ()
modifySignature f = do
  sig <- getSignature
  putSignature $ f sig

-- Definitions operations
------------------------------------------------------------------------

addDefinition :: IsTerm t => Name -> Definition t -> TC t v ()
addDefinition x def' =
  modifySignature $ \sig -> Sig.addDefinition sig x def'

getDefinition :: IsTerm t => Name -> TC t v (Definition t)
getDefinition name = atSrcLoc name $ do
  sig <- getSignature
  return $ Sig.getDefinition sig name

-- MetaVar operations
------------------------------------------------------------------------

addMetaVar :: IsTerm t => Closed (Type t) -> TC t v MetaVar
addMetaVar type_ = do
    sig <- getSignature
    let (mv, sig') = Sig.addMetaVar sig type_
    putSignature sig'
    return mv

instantiateMetaVar :: IsTerm t => MetaVar -> Closed (Term t) -> TC t v ()
instantiateMetaVar mv t = do
  modifySignature $ \sig -> Sig.instantiateMetaVar sig mv t

getTypeOfMetaVar :: IsTerm t => MetaVar -> TC t v (Closed (Type t))
getTypeOfMetaVar mv = do
  sig <- getSignature
  return $ Sig.getMetaVarType sig mv

getBodyOfMetaVar :: IsTerm t => MetaVar -> TC t v (Maybe (Closed (Term t)))
getBodyOfMetaVar mv = do
  sig <- getSignature
  return $ Sig.getMetaVarBody sig mv

-- Operations on the context
------------------------------------------------------------------------

liftClosed :: ClosedTC t a -> TC t v a
liftClosed = localContext $ const Ctx.Empty

extendContext
    :: (IsTerm t)
    => Name -> Type t v -> (TermVar v -> TC t (TermVar v) a)
    -> TC t v a
extendContext n type_ m =
    localContext (`Ctx.Snoc` (n, type_)) $ m (boundTermVar n)

getTypeOfName :: (IsTerm t) => Name -> TC t v (Maybe (v, Type t v))
getTypeOfName n = do
    ctx <- askContext
    return $ Ctx.lookupName n ctx

getTypeOfVar :: (IsTerm t) => v -> TC t v (Type t v)
getTypeOfVar v = do
    ctx <- askContext
    return $ Ctx.getVar v ctx

-- Problem handling
------------------------------------------------------------------------

newProblem_
    :: (Typeable a, Typeable v, Typeable t, PP.Pretty p)
    => MetaVar -> p -> (Closed (Term t) -> StuckTC t v a) -> TC t v (ProblemId t v a)
newProblem_ mv = newProblem (Set.singleton mv)
