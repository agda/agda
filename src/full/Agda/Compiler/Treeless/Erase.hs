{-# LANGUAGE CPP #-}
{-# LANGUAGE PatternSynonyms #-}

module Agda.Compiler.Treeless.Erase (eraseTerms, computeErasedConstructorArgs) where

import Control.Arrow ((&&&), (***), first, second)
import Control.Monad
import Control.Monad.State
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Semigroup

import Agda.Syntax.Common
import Agda.Syntax.Internal as I
import Agda.Syntax.Abstract.Name (QName)
import Agda.Syntax.Position
import Agda.Syntax.Treeless
import Agda.Syntax.Literal

import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Monad as I
import Agda.TypeChecking.Monad.Builtin
import Agda.TypeChecking.Telescope
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Datatypes
import Agda.TypeChecking.Pretty hiding ((<>))
import Agda.TypeChecking.Primitive

import Agda.Compiler.Treeless.Subst
import Agda.Compiler.Treeless.Pretty
import Agda.Compiler.Treeless.Unused

import Agda.Utils.Functor
import Agda.Utils.Lens
import Agda.Utils.Maybe
import Agda.Utils.Memo
import Agda.Utils.Monad
import Agda.Utils.Pretty (prettyShow)
import qualified Agda.Utils.Pretty as P
import Agda.Utils.IntSet.Infinite (IntSet)
import qualified Agda.Utils.IntSet.Infinite as IntSet

#include "undefined.h"
import Agda.Utils.Impossible

data ESt = ESt { _funMap  :: Map QName FunInfo
               , _typeMap :: Map QName TypeInfo }

funMap :: Lens' (Map QName FunInfo) ESt
funMap f r = f (_funMap r) <&> \ a -> r { _funMap = a }

typeMap :: Lens' (Map QName TypeInfo) ESt
typeMap f r = f (_typeMap r) <&> \ a -> r { _typeMap = a }

type E = StateT ESt TCM

runE :: E a -> TCM a
runE m = evalStateT m (ESt Map.empty Map.empty)

-- | Takes the name of the data/record type.
computeErasedConstructorArgs :: QName -> TCM ()
computeErasedConstructorArgs d = do
  cs <- getConstructors d
  runE $ mapM_ getFunInfo cs

eraseTerms :: QName -> EvaluationStrategy -> TTerm -> TCM TTerm
eraseTerms q eval t = usedArguments q t *> runE (eraseTop q t)
  where
    eraseTop q t = do
      (_, h) <- getFunInfo q
      case h of
        Erasable -> pure TErased
        Empty    -> pure TErased
        _        -> erase t

    erase t = case tAppView t of

      TCon c : vs -> do
        (rs, h) <- getFunInfo c
        when (length rs < length vs) __IMPOSSIBLE__
        case h of
          Erasable -> pure TErased
          Empty    -> pure TErased
          _        -> tApp (TCon c) <$> zipWithM eraseRel rs vs

      TDef f : vs -> do
        (rs, h) <- getFunInfo f
        case h of
          Erasable -> pure TErased
          Empty    -> pure TErased
          _        -> tApp (TDef f) <$> zipWithM eraseRel (rs ++ repeat NotErasable) vs

      _ -> case t of
        TVar{}         -> pure t
        TDef{}         -> pure t
        TPrim{}        -> pure t
        TLit{}         -> pure t
        TCon{}         -> pure t
        TApp f es      -> tApp <$> erase f <*> mapM erase es
        TLam b         -> tLam <$> erase b
        TLet e b       -> do
          e <- erase e
          if isErased e
            then case b of
                   TCase 0 _ _ _ -> tLet TErased <$> erase b
                   _             -> erase $ subst 0 TErased b
            else tLet e <$> erase b
        TCase x t d bs -> do
          (d, bs) <- pruneUnreachable x (caseType t) d bs
          d       <- erase d
          bs      <- mapM eraseAlt bs
          tCase x t d bs

        TUnit          -> pure t
        TSort          -> pure t
        TErased        -> pure t
        TError{}       -> pure t
        TCoerce e      -> TCoerce <$> erase e

    -- #3380: this is not safe for strict backends
    tLam TErased | eval == LazyEvaluation = TErased
    tLam t                                = TLam t

    tLet e b
      | freeIn 0 b = TLet e b
      | otherwise  = strengthen __IMPOSSIBLE__ b

    tApp f []                  = f
    tApp TErased _             = TErased
    tApp f _ | isUnreachable f = tUnreachable
    tApp f es                  = TApp f es

    tCase x t d bs
      | isErased d && all (isErased . aBody) bs = pure TErased
      | otherwise = case bs of
        [TACon c a b] -> do
          h <- snd <$> getFunInfo c
          case h of
            NotErasable -> noerase
            Empty       -> pure TErased
            Erasable    -> (if a == 0 then pure else erase) $ applySubst (replicate a TErased ++# idS) b
                              -- might enable more erasure
        _ -> noerase
      where
        noerase = pure $ TCase x t d bs

    isErased t = t == TErased || isUnreachable t

    eraseRel r t | erasable r = pure TErased
                 | otherwise  = erase t

    eraseAlt a = case a of
      TALit l b   -> TALit l   <$> erase b
      TACon c a b -> do
        rs <- map erasable . fst <$> getFunInfo c
        let sub = foldr (\ e -> if e then (TErased :#) . wkS 1 else liftS 1) idS $ reverse rs
        TACon c a <$> erase (applySubst sub b)
      TAGuard g b -> TAGuard   <$> erase g <*> erase b

-- | Doesn't have any type information (other than the name of the data type),
--   so we can't do better than checking if all constructors are present.
pruneUnreachable :: Int -> CaseType -> TTerm -> [TAlt] -> E (TTerm, [TAlt])
pruneUnreachable _ (CTData q) d bs = do
  cs <- lift $ getConstructors q
  let complete =length cs == length [ b | b@TACon{} <- bs ]
  let d' | complete  = tUnreachable
         | otherwise = d
  return (d', bs)
pruneUnreachable x CTNat d bs = return $ pruneIntCase x d bs (IntSet.below 0)
pruneUnreachable x CTInt d bs = return $ pruneIntCase x d bs IntSet.empty
pruneUnreachable _ _ d bs = pure (d, bs)

-- These are the guards we generate for Int/Nat pattern matching
pattern Below :: Range -> Int -> Integer -> TTerm
pattern Below r x n = TApp (TPrim PLt)  [TVar x, TLit (LitNat r n)]

pattern Above :: Range -> Int -> Integer -> TTerm
pattern Above r x n = TApp (TPrim PGeq) [TVar x, TLit (LitNat r n)]

-- | Strip unreachable clauses (replace by tUnreachable for the default).
--   Fourth argument is the set of ints covered so far.
pruneIntCase :: Int -> TTerm -> [TAlt] -> IntSet -> (TTerm, [TAlt])
pruneIntCase x d bs cover = go bs cover
  where
    go [] cover
      | cover == IntSet.full = (tUnreachable, [])
      | otherwise            = (d, [])
    go (b : bs) cover =
      case b of
        TAGuard (Below _ y n) _ | x == y -> rec (IntSet.below n)
        TAGuard (Above _ y n) _ | x == y -> rec (IntSet.above n)
        TALit (LitNat _ n) _             -> rec (IntSet.singleton n)
        _                                -> second (b :) $ go bs cover
      where
        rec this = second addAlt $ go bs cover'
          where
            this'  = IntSet.difference this cover
            cover' = this' <> cover
            addAlt = case IntSet.toFiniteList this' of
                       Just []  -> id                                     -- unreachable case
                       Just [n] -> (TALit (LitNat noRange n) (aBody b) :) -- possibly refined case
                       _        -> (b :)                                  -- unchanged case

data TypeInfo = Empty | Erasable | NotErasable
  deriving (Eq, Show)

sumTypeInfo :: [TypeInfo] -> TypeInfo
sumTypeInfo is = foldr plus Empty is
  where
    plus Empty       r           = r
    plus r           Empty       = r
    plus Erasable    r           = r
    plus r           Erasable    = r
    plus NotErasable NotErasable = NotErasable

erasable :: TypeInfo -> Bool
erasable Erasable    = True
erasable Empty       = True
erasable NotErasable = False

type FunInfo = ([TypeInfo], TypeInfo)

getFunInfo :: QName -> E FunInfo
getFunInfo q = memo (funMap . key q) $ getInfo q
  where
    getInfo q = do
      (rs, t) <- do
        (tel, t) <- lift $ typeWithoutParams q
        is     <- mapM (getTypeInfo . snd . dget) tel
        used   <- lift $ (++ repeat True) <$> getCompiledArgUse q
        forced <- lift $ (++ repeat NotForced) <$> getForcedArgs q
        return (zipWith3 (uncurry . mkR . getModality) tel (zip forced used) is, t)
      h <- if isAbsurdLambdaName q then pure Erasable else getTypeInfo t
      lift $ reportSLn "treeless.opt.erase.info" 50 $ "type info for " ++ prettyShow q ++ ": " ++ show rs ++ " -> " ++ show h
      lift $ setErasedConArgs q $ map erasable rs
      return (rs, h)

    -- Treat empty, erasable, or unused arguments as Erasable
    mkR :: Modality -> IsForced -> Bool -> TypeInfo -> TypeInfo
    mkR m f b i
      | not (usableModality m) = Erasable
      | not b                  = Erasable
      | Forced <- f            = Erasable
      | otherwise              = i

telListView :: Type -> TCM (ListTel, Type)
telListView t = do
  TelV tel t <- telView t
  return (telToList tel, t)

typeWithoutParams :: QName -> TCM (ListTel, Type)
typeWithoutParams q = do
  def <- getConstInfo q
  let d = case I.theDef def of
        Function{ funProjection = Just Projection{ projIndex = i } } -> i - 1
        Constructor{ conPars = n } -> n
        _                          -> 0
  first (drop d) <$> telListView (defType def)

getTypeInfo :: Type -> E TypeInfo
getTypeInfo t0 = do
  (tel, t) <- lift $ telListView t0
  et <- case I.unEl t of
    I.Def d _ -> do
      -- #2916: Only update the memo table for d. Results for other types are
      -- under the assumption that d is erasable!
      oldMap <- use typeMap
      dInfo <- typeInfo d
      typeMap .= Map.insert d dInfo oldMap
      return dInfo
    Sort{}    -> return Erasable
    _         -> return NotErasable
  is <- mapM (getTypeInfo . snd . dget) tel
  let e | any (== Empty) is = Erasable
        | null is           = et        -- TODO: guard should really be "all inhabited is"
        | et == Empty       = Erasable
        | otherwise         = et
  lift $ reportSDoc "treeless.opt.erase.type" 50 $ prettyTCM t0 <+> text ("is " ++ show e)
  return e
  where
    typeInfo :: QName -> E TypeInfo
    typeInfo q = memoRec (typeMap . key q) Erasable $ do  -- assume recursive occurrences are erasable
      msizes <- lift $ mapM getBuiltinName
                         [builtinSize, builtinSizeLt]
      def    <- lift $ getConstInfo q
      mcs    <- return $ case I.theDef def of
        I.Datatype{ dataCons = cs } -> Just cs
        I.Record{ recConHead = c }  -> Just [conName c]
        _                           -> Nothing
      case mcs of
        _ | Just q `elem` msizes -> return Erasable
        Just [c] -> do
          (ts, _) <- lift $ typeWithoutParams c
          let rs = map getModality ts
          is <- mapM (getTypeInfo . snd . dget) ts
          let er = and [ erasable i || not (usableModality r) | (i, r) <- zip is rs ]
          return $ if er then Erasable else NotErasable
        Just []      -> return Empty
        Just (_:_:_) -> return NotErasable
        Nothing ->
          case I.theDef def of
            I.Function{ funClauses = cs } ->
              sumTypeInfo <$> mapM (maybe (return Empty) (getTypeInfo . El __DUMMY_SORT__) . clauseBody) cs
            _ -> return NotErasable
