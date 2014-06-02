module Types.Monad
    ( -- * Monad definition
      TC
    , ClosedTC
    , runTC
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
    , addFreshMetaVar
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
    , bindProblem
    , waitOnProblem
    ) where

import Prelude                                    hiding (abs, pi)

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

addFreshMetaVar :: IsTerm t => Closed (Type t) -> TC t v MetaVar
addFreshMetaVar type_ = do
    sig <- getSignature
    let (mv, sig') = Sig.addFreshMetaVar sig type_
    putSignature sig'
    return mv

instantiateMetaVar :: IsTerm t => MetaVar -> Closed (Term t) -> TC t v ()
instantiateMetaVar mv t = do
  modifySignature $ \sig -> Sig.instantiateMetaVar sig mv t

getTypeOfMetaVar :: IsTerm t => MetaVar -> TC t v (Closed (Type t))
getTypeOfMetaVar mv = do
  sig <- getSignature
  return $ case Sig.getMetaInst sig mv of
    Sig.Inst mvType _ -> mvType
    Sig.Open mvType   -> mvType

getBodyOfMetaVar :: IsTerm t => MetaVar -> TC t v (Maybe (Closed (Term t)))
getBodyOfMetaVar mv = do
  sig <- getSignature
  return $ case Sig.getMetaInst sig mv of
    Sig.Inst _ mvBody -> Just mvBody
    Sig.Open _        -> Nothing

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

