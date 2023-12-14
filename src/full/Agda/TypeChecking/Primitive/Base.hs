{-# LANGUAGE ApplicativeDo #-}

module Agda.TypeChecking.Primitive.Base where

import Control.Monad             ( mzero )
import Control.Monad.Fail        ( MonadFail )
  -- Control.Monad.Fail import is redundant since GHC 8.8.1
import Control.Monad.Trans.Maybe ( MaybeT(..), runMaybeT )

import qualified Data.Map as Map

import Agda.Syntax.Common
import Agda.Syntax.Internal

import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Monad.Builtin
import Agda.TypeChecking.Monad.Context
import Agda.TypeChecking.Monad.Debug
import Agda.TypeChecking.Names
import {-# SOURCE #-} Agda.TypeChecking.Primitive
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Reduce ( reduce )
import Agda.TypeChecking.Monad.Signature
import Agda.TypeChecking.Substitute

import Agda.Utils.Functor
import Agda.Utils.Impossible
import Agda.Utils.Maybe
import Agda.Syntax.Common.Pretty ( prettyShow )

-- Type combinators

infixr 4 -->
infixr 4 .-->
infixr 4 ..-->

(-->), (.-->), (..-->) :: Applicative m => m Type -> m Type -> m Type
a --> b = garr id a b
a .--> b = garr (const $ Irrelevant) a b
a ..--> b = garr (const $ NonStrict) a b

garr :: Applicative m => (Relevance -> Relevance) -> m Type -> m Type -> m Type
garr f a b = do
  a' <- a
  b' <- b
  pure $ El (funSort (getSort a') (getSort b')) $
    Pi (mapRelevance f $ defaultDom a') (NoAbs "_" b')

gpi :: (MonadAddContext m, MonadDebug m)
    => ArgInfo -> String -> m Type -> m Type -> m Type
gpi info name a b = do
  a <- a
  let dom :: Dom Type
      dom = defaultNamedArgDom info name a
  b <- addContext (name, dom) b
  let y = stringToArgName name
  return $ El (mkPiSort dom (Abs y b))
              (Pi dom (Abs y b))

hPi, nPi :: (MonadAddContext m, MonadDebug m)
         => String -> m Type -> m Type -> m Type
hPi = gpi $ setHiding Hidden defaultArgInfo
nPi = gpi defaultArgInfo

hPi', nPi' :: (MonadFail m, MonadAddContext m, MonadDebug m)
           => String -> NamesT m Type -> (NamesT m Term -> NamesT m Type) -> NamesT m Type
hPi' s a b = hPi s a (bind' s (\ x -> b x))
nPi' s a b = nPi s a (bind' s (\ x -> b x))

{-# INLINABLE pPi' #-}
pPi' :: (MonadAddContext m, HasBuiltins m, MonadDebug m)
     => String -> NamesT m Term -> (NamesT m Term -> NamesT m Type) -> NamesT m Type
pPi' n phi b = toFinitePi <$> nPi' n (elSSet $ cl isOne <@> phi) b
 where
   isOne = fromMaybe __IMPOSSIBLE__ <$> getBuiltin' builtinIsOne

-- | Turn a 'Pi' type into one whose domain is annotated finite, i.e.,
-- one that represents a @Partial@ element rather than an actual
-- function.
toFinitePi :: Type -> Type
toFinitePi (El s (Pi d b)) = El s $ Pi
  (setRelevance Irrelevant $ d { domIsFinite = True })
  b
toFinitePi _ = __IMPOSSIBLE__

el' :: Applicative m => m Term -> m Term -> m Type
el' l a = El <$> (tmSort <$> l) <*> a

els :: Applicative m => m Sort -> m Term -> m Type
els l a = El <$> l <*> a

el's :: Applicative m => m Term -> m Term -> m Type
el's l a = El <$> (SSet . atomicLevel <$> l) <*> a

elInf :: Functor m => m Term -> m Type
elInf t = (El (Inf UType 0) <$> t)

elSSet :: Functor m => m Term -> m Type
elSSet t = (El (SSet $ ClosedLevel 0) <$> t)

nolam :: Term -> Term
nolam = Lam defaultArgInfo . NoAbs "_"

varM :: Applicative m => Int -> m Term
varM = pure . var

infixl 9 <@>, <#>

gApply :: Applicative m => Hiding -> m Term -> m Term -> m Term
gApply h a b = gApply' (setHiding h defaultArgInfo) a b

gApply' :: Applicative m => ArgInfo -> m Term -> m Term -> m Term
gApply' info a b = do
    x <- a
    y <- b
    pure $ x `apply` [Arg info y]

(<@>),(<#>),(<..>) :: Applicative m => m Term -> m Term -> m Term
(<@>) = gApply NotHidden
(<#>) = gApply Hidden
(<..>) = gApply' (setRelevance Irrelevant defaultArgInfo)

(<@@>) :: Applicative m => m Term -> (m Term,m Term,m Term) -> m Term
t <@@> (x,y,r) = do
  t <- t
  x <- x
  y <- y
  r <- r
  pure $ t `applyE` [IApply x y r]

list :: TCM Term -> TCM Term
list t = primList <@> t

tMaybe :: TCM Term -> TCM Term
tMaybe t = primMaybe <@> t

io :: TCM Term -> TCM Term
io t = primIO <@> t

path :: TCM Term -> TCM Term
path t = primPath <@> t

el :: Functor m => m Term -> m Type
el t = El (mkType 0) <$> t

-- | The universe @Set0@ as a type.
tset :: Applicative m => m Type
tset = pure $ sort (mkType 0)

-- | @SizeUniv@ as a sort.
sSizeUniv :: Sort
sSizeUniv = SizeUniv

-- | @SizeUniv@ as a type.
tSizeUniv :: Applicative m => m Type
tSizeUniv = pure $ sort sSizeUniv

tLevelUniv :: Applicative m => m Type
tLevelUniv = pure $ sort $ LevelUniv

-- | Abbreviation: @argN = 'Arg' 'defaultArgInfo'@.
argN :: e -> Arg e
argN = Arg defaultArgInfo

domN :: e -> Dom e
domN = defaultDom

-- | Abbreviation: @argH = 'hide' 'Arg' 'defaultArgInfo'@.
argH :: e -> Arg e
argH = Arg $ setHiding Hidden defaultArgInfo

domH :: e -> Dom e
domH = setHiding Hidden . defaultDom

---------------------------------------------------------------------------
-- * Accessing the primitive functions
---------------------------------------------------------------------------

lookupPrimitiveFunction :: PrimitiveId -> TCM PrimitiveImpl
lookupPrimitiveFunction x =
  fromMaybe (do
                reportSDoc "tc.prim" 20 $ "Lookup of primitive function" <+> pretty x <+> "failed"
                typeError $ NoSuchPrimitiveFunction (getBuiltinId x))
            (Map.lookup x primitiveFunctions)

lookupPrimitiveFunctionQ :: QName -> TCM (PrimitiveId, PrimitiveImpl)
lookupPrimitiveFunctionQ q = do
  let s = prettyShow (nameCanonical $ qnameName q)
  case primitiveById s of
    Nothing -> typeError $ NoSuchPrimitiveFunction s
    Just s -> do
      PrimImpl t pf <- lookupPrimitiveFunction s
      return (s, PrimImpl t $ pf { primFunName = q })

getBuiltinName :: (HasBuiltins m, MonadReduce m) => BuiltinId -> m (Maybe QName)
getBuiltinName b = runMaybeT $ getQNameFromTerm =<< MaybeT (getBuiltin' b)

-- | Convert a name in 'Term' form back to 'QName'.
--
getQNameFromTerm :: MonadReduce m => Term -> MaybeT m QName
getQNameFromTerm v = do
    v <- reduce v
    case unSpine v of
      Def x _   -> return x
      Con x _ _ -> return $ conName x
      Lam _ b   -> getQNameFromTerm $ unAbs b
      _ -> mzero

isBuiltin :: (HasBuiltins m, MonadReduce m) => QName -> BuiltinId -> m Bool
isBuiltin q b = (Just q ==) <$> getBuiltinName b

------------------------------------------------------------------------
-- * Builtin Sigma
------------------------------------------------------------------------

data SigmaKit = SigmaKit
  { sigmaName :: QName
  , sigmaCon  :: ConHead
  , sigmaFst  :: QName
  , sigmaSnd  :: QName
  }
  deriving (Eq,Show)

getSigmaKit :: (HasBuiltins m, HasConstInfo m) => m (Maybe SigmaKit)
getSigmaKit = do
  ms <- getBuiltinName' builtinSigma
  case ms of
    Nothing -> return Nothing
    Just sigma -> do
      def <- theDef <$> getConstInfo sigma
      case def of
        Record { recFields = [fst,snd], recConHead = con } -> do
          return . Just $ SigmaKit
            { sigmaName = sigma
            , sigmaCon  = con
            , sigmaFst  = unDom fst
            , sigmaSnd  = unDom snd
            }
        _ -> __IMPOSSIBLE__  -- This invariant is ensured in bindBuiltinSigma
