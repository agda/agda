module Agda.TypeChecking.Primitive.Base where

-- Control.Monad.Fail import is redundant since GHC 8.8.1
import Control.Monad.Fail (MonadFail)

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
import Agda.Utils.Pretty ( prettyShow )

-- Type combinators

infixr 4 -->
infixr 4 .-->
infixr 4 ..-->

(-->), (.-->), (..-->) :: Monad tcm => tcm Type -> tcm Type -> tcm Type
a --> b = garr id a b
a .--> b = garr (const $ Irrelevant) a b
a ..--> b = garr (const $ NonStrict) a b

garr :: Monad m => (Relevance -> Relevance) -> m Type -> m Type -> m Type
garr f a b = do
  a' <- a
  b' <- b
  return $ El (funSort (getSort a') (getSort b')) $
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
hPi' s a b = hPi s a (bind' s b)
nPi' s a b = nPi s a (bind' s b)

pPi' :: (MonadAddContext m, HasBuiltins m, MonadDebug m)
     => String -> NamesT m Term -> (NamesT m Term -> NamesT m Type) -> NamesT m Type
pPi' n phi b = toFinitePi <$> nPi' n (elSSet $ cl isOne <@> phi) b
 where
   toFinitePi :: Type -> Type
   toFinitePi (El s (Pi d b)) = El s $ Pi (setRelevance Irrelevant $ d { domFinite = True }) b
   toFinitePi _               = __IMPOSSIBLE__

   isOne = fromMaybe __IMPOSSIBLE__ <$> getBuiltin' builtinIsOne

el' :: Monad m => m Term -> m Term -> m Type
el' l a = El <$> (tmSort <$> l) <*> a

el's :: Monad m => m Term -> m Term -> m Type
el's l a = El <$> (SSet . atomicLevel <$> l) <*> a

elInf :: Functor m => m Term -> m Type
elInf t = (El (Inf IsFibrant 0) <$> t)

elSSet :: Functor m => m Term -> m Type
elSSet t = (El (SSet $ ClosedLevel 0) <$> t)

nolam :: Term -> Term
nolam = Lam defaultArgInfo . NoAbs "_"

varM :: Monad tcm => Int -> tcm Term
varM = return . var

infixl 9 <@>, <#>

gApply :: Monad tcm => Hiding -> tcm Term -> tcm Term -> tcm Term
gApply h a b = gApply' (setHiding h defaultArgInfo) a b

gApply' :: Monad tcm => ArgInfo -> tcm Term -> tcm Term -> tcm Term
gApply' info a b = do
    x <- a
    y <- b
    return $ x `apply` [Arg info y]

(<@>),(<#>),(<..>) :: Monad tcm => tcm Term -> tcm Term -> tcm Term
(<@>) = gApply NotHidden
(<#>) = gApply Hidden
(<..>) = gApply' (setRelevance Irrelevant defaultArgInfo)

(<@@>) :: Monad tcm => tcm Term -> (tcm Term,tcm Term,tcm Term) -> tcm Term
t <@@> (x,y,r) = do
  t <- t
  x <- x
  y <- y
  r <- r
  return $ t `applyE` [IApply x y r]

list :: TCM Term -> TCM Term
list t = primList <@> t

tMaybe :: TCM Term -> TCM Term
tMaybe t = primMaybe <@> t

io :: TCM Term -> TCM Term
io t = primIO <@> t

path :: TCM Term -> TCM Term
path t = primPath <@> t

el :: Functor tcm => tcm Term -> tcm Type
el t = El (mkType 0) <$> t

tset :: Monad tcm => tcm Type
tset = return $ sort (mkType 0)

sSizeUniv :: Sort
sSizeUniv = mkType 0
-- Andreas, 2016-04-14 switching off SizeUniv, unfixing issue #1428
-- sSizeUniv = SizeUniv

tSizeUniv :: Monad tcm => tcm Type
tSizeUniv = tset
-- Andreas, 2016-04-14 switching off SizeUniv, unfixing issue #1428
-- tSizeUniv = return $ El sSizeUniv $ Sort sSizeUniv
-- Andreas, 2015-03-16 Since equality checking for types
-- includes equality checking for sorts, we cannot put
-- SizeUniv in Setω.  (SizeUniv : Setω) == (_0 : suc _0)
-- will first instantiate _0 := Setω, which is wrong.
-- tSizeUniv = return $ El Inf $ Sort SizeUniv

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

lookupPrimitiveFunction :: String -> TCM PrimitiveImpl
lookupPrimitiveFunction x =
  fromMaybe (do
                reportSDoc "tc.prim" 20 $ "Lookup of primitive function" <+> text x <+> "failed"
                typeError $ NoSuchPrimitiveFunction x)
            (Map.lookup x primitiveFunctions)

lookupPrimitiveFunctionQ :: QName -> TCM (String, PrimitiveImpl)
lookupPrimitiveFunctionQ q = do
  let s = prettyShow (nameCanonical $ qnameName q)
  PrimImpl t pf <- lookupPrimitiveFunction s
  return (s, PrimImpl t $ pf { primFunName = q })

getBuiltinName :: String -> TCM (Maybe QName)
getBuiltinName b = do
  caseMaybeM (getBuiltin' b) (return Nothing) (Just <.> getName)
  where
  getName v = do
    v <- reduce v
    case unSpine $ v of
      Def x _   -> return x
      Con x _ _ -> return $ conName x
      Lam _ b   -> getName $ unAbs b
      _ -> __IMPOSSIBLE__

isBuiltin :: QName -> String -> TCM Bool
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
        _ -> __IMPOSSIBLE__
