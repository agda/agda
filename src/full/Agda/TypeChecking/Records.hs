{-# LANGUAGE CPP #-}

module Agda.TypeChecking.Records where

import Control.Applicative
import Control.Arrow ((***))
import Control.Monad
import Data.List
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Function

import Agda.Syntax.Common
import qualified Agda.Syntax.Concrete.Name as C
import Agda.Syntax.Abstract.Name
import Agda.Syntax.Internal
import Agda.Syntax.Position
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Telescope
import Agda.TypeChecking.Datatypes
import Agda.Utils.Either
import Agda.Utils.List
import Agda.Utils.Maybe
import Agda.Utils.Monad

#include "../undefined.h"
import Agda.Utils.Impossible

-- | Order the fields of a record construction.
--   Use the second argument for missing fields.
orderFields :: QName -> a -> [C.Name] -> [(C.Name, a)] -> TCM [a]
orderFields r def xs fs = do
  shouldBeNull (ys \\ nub ys) $ DuplicateFields . nub
  shouldBeNull (ys \\ xs)     $ TooManyFields r
  -- shouldBeNull (xs \\ ys)     $ TooFewFields r
  return $ order xs fs
  where
    ys = map fst fs

    shouldBeNull [] err = return ()
    shouldBeNull xs err = typeError $ err xs

    -- invariant: the first list contains at least the fields of the second list
    order [] [] = []
    order [] _  = __IMPOSSIBLE__
    order (x : xs) ys = case lookup x (assocHoles ys) of
      Just (e, ys') -> e : order xs ys'
      Nothing       -> def : order xs ys

    assocHoles xs = [ (x, (v, xs')) | ((x, v), xs') <- holes xs ]

-- | The name of the module corresponding to a record.
recordModule :: QName -> ModuleName
recordModule = mnameFromList . qnameToList

-- | Get the definition for a record. Throws an exception if the name
--   does not refer to a record.
getRecordDef :: QName -> TCM Defn
getRecordDef r = do
  def <- theDef <$> getConstInfo r
  case def of
    Record{} -> return def
    _        -> typeError $ ShouldBeRecordType (El Prop $ Def r [])

-- | Get the field names of a record.
getRecordFieldNames :: QName -> TCM [Arg C.Name]
getRecordFieldNames r =
  map (fmap (nameConcrete . qnameName)) . recFields <$> getRecordDef r

-- | Find all records with at least the given fields.
findPossibleRecords :: [C.Name] -> TCM [QName]
findPossibleRecords fields = do
  defs <- (Map.union `on` sigDefinitions) <$> getSignature <*> getImportedSignature
  let possible def = case theDef def of
        Record{ recFields = fs } -> Set.isSubsetOf given inrecord
          where inrecord = Set.fromList $ map (nameConcrete . qnameName . unArg) fs
        _ -> False
  return [ defName d | d <- Map.elems defs, possible d ]
  where
    given = Set.fromList fields

-- | Get the field types of a record.
getRecordFieldTypes :: QName -> TCM Telescope
getRecordFieldTypes r = recTel <$> getRecordDef r

-- | Get the type of the record constructor.
getRecordConstructorType :: QName -> TCM Type
getRecordConstructorType r = recConType <$> getRecordDef r

-- | Returns the given record type's constructor name (with an empty
-- range).
getRecordConstructor :: QName -> TCM QName
getRecordConstructor r = killRange <$> recCon <$> getRecordDef r

-- | Check if a name refers to a record.
--   If yes, return record definition.
isRecord :: QName -> TCM (Maybe Defn)
isRecord r = do
  def <- theDef <$> getConstInfo r
  return $ case def of
    Record{} -> Just def
    _        -> Nothing

-- | Check if a name refers to an eta expandable record.
isEtaRecord :: QName -> TCM Bool
isEtaRecord r = do
  def <- theDef <$> getConstInfo r
  return $ case def of
    Record{recEtaEquality = eta} -> eta
    _                            -> False

-- | Check if a type is an eta expandable record and return the record identifier and the parameters.
isEtaRecordType :: Type -> TCM (Maybe (QName, Args))
isEtaRecordType (El _ (Def d ps)) = ifM (isEtaRecord d) (return $ Just (d, ps)) (return Nothing)
isEtaRecordType _ = return Nothing

-- | Check if a name refers to a record constructor.
--   If yes, return record definition.
isRecordConstructor :: QName -> TCM (Maybe Defn)
isRecordConstructor c = do
  def <- theDef <$> getConstInfo c
  case def of
    Constructor{ conData = r } -> isRecord r
    _                          -> return Nothing

-- | Check if a constructor name is the internally generated record constructor.
isGeneratedRecordConstructor :: QName -> TCM Bool
isGeneratedRecordConstructor c = do
  def <- theDef <$> getConstInfo c
  case def of
    Constructor{ conData = r } -> do
      def <- theDef <$> getConstInfo r
      case def of
        Record{ recNamedCon = False } -> return True
        _                             -> return False
    _ -> return False

{-| Compute the eta expansion of a record. The first argument should be
    the name of a record type. Given

    @record R : Set where x : A; y : B; .z : C@

    and @r : R@, @etaExpand R [] r@ is @[R.x r, R.y r, DontCare]@
-}
etaExpandRecord :: QName -> Args -> Term -> TCM (Telescope, Args)
etaExpandRecord r pars u = do
  Record{ recFields = xs, recTel = tel } <- getRecordDef r
  let tel' = apply tel pars
  case u of
    Con _ args -> return (tel', args)  -- Already expanded.
    _          -> do
{- STALE
      -- irrelevant fields are expanded to DontCare
      -- this is sound because etaExpandRecord is only called during conversion
      -- WARNING: do not use etaExpandRecord to expand MetaVars!!
      let proj (Arg h Irrelevant x) = Arg h Irrelevant $ DontCare (Def x [defaultArg u])
          proj (Arg h rel x)        = Arg h rel $
            Def x [defaultArg u]
          xs' = map proj xs
-}
      let xs' = map (fmap (\ x -> Def x [defaultArg u])) xs
      reportSDoc "tc.record.eta" 20 $ vcat
        [ text "eta expanding" <+> prettyTCM u <+> text ":" <+> prettyTCM r
        , nest 2 $ vcat
          [ text "tel' =" <+> prettyTCM tel'
          , text "args =" <+> prettyTCM xs'
          ]
        ]
      return (tel', xs')
{- UNUSED
  where
    hide a = a { argHiding = Hidden }
-}

-- | The fields should be eta contracted already.
--
--   We can eta constract if all fields @f = ...@ are irrelevant
--   or the corresponding projection @f = f v@ of the same value @v@,
--   but we need at least one relevant field to find the value @v@.
etaContractRecord :: QName -> QName -> Args -> TCM Term
etaContractRecord r c args = do
  Record{ recPars = npars, recFields = xs } <- getRecordDef r
  let check :: Arg Term -> Arg QName -> Maybe (Maybe Term)
      check a ax = do
      -- @a@ is the constructor argument, @ax@ the corr. record field name
        -- skip irrelevant record fields by returning DontCare
        case (argRelevance a, unArg a) of
          (Irrelevant, v) -> Just Nothing
          -- if @a@ is the record field name applied to a single argument
          -- then it passes the check
          (_, Def f [arg]) | unArg ax == f
                         -> Just $ Just $ unArg arg
          _              -> Nothing
      fallBack = return (Con c args)
  case compare (length args) (length xs) of
    LT -> fallBack       -- Not fully applied
    GT -> __IMPOSSIBLE__ -- Too many arguments. Impossible.
    EQ -> do
      case zipWithM check args xs of
        Just as -> case [ a | Just a <- as ] of
          (a:as) ->
            if all (a ==) as
              then do
                reportSDoc "tc.record.eta" 15 $ vcat
                  [ text "record" <+> prettyTCM (Con c args)
                  , text "is eta-contracted to" <+> prettyTCM a
                  ]
                return a
              else fallBack
          _ -> fallBack -- just irrelevant terms
        _ -> fallBack  -- a Nothing

{- OLD CODE, uses DontCare
-- | The fields should be eta contracted already.
etaContractRecord :: QName -> QName -> Args -> TCM Term
etaContractRecord r c args = do
  Record{ recPars = npars, recFields = xs } <- getRecordDef r
  let check :: Arg Term -> Arg QName -> Maybe Term
      check a ax = do
      -- @a@ is the constructor argument, @ax@ the corr. record field name
        -- skip irrelevant record fields by returning DontCare
        case (argRelevance a, unArg a) of
          (Irrelevant, v) -> return $ Just $ DontCare __IMPOSSIBLE__ -- thrown out later
          -- if @a@ is the record field name applied to a single argument
          -- then it passes the check
          (_, Def y [arg]) | unArg ax == y
                         -> return (Just $ unArg arg)
          _              -> return Nothing
      fallBack = return (Con c args)
  case compare (length args) (length xs) of
    LT -> fallBack       -- Not fully applied
    GT -> __IMPOSSIBLE__ -- Too many arguments. Impossible.
    EQ -> do
      as <- zipWithM check args xs
      case sequence as of
        Just as -> case filter notDontCare as of
          (a:as) ->
            if all (a ==) as
              then do
                reportSDoc "tc.record.eta" 15 $ vcat
                  [ text "record" <+> prettyTCM (Con c args)
                  , text "is eta-contracted to" <+> prettyTCM a
                  ]
                return a
              else fallBack
          _ -> fallBack -- just DontCares
        _ -> fallBack  -- a Nothing
  where notDontCare (DontCare _) = False
        notDontCare _            = True
-}

-- | Is the type a hereditarily singleton record type? May return a
-- blocking metavariable.
--
-- Precondition: The name should refer to a record type, and the
-- arguments should be the parameters to the type.
isSingletonRecord :: QName -> Args -> TCM (Either MetaId Bool)
isSingletonRecord r ps = mapRight isJust <$> isSingletonRecord' False r ps

isSingletonRecordModuloRelevance :: QName -> Args -> TCM (Either MetaId Bool)
isSingletonRecordModuloRelevance r ps = mapRight isJust <$> isSingletonRecord' True r ps

-- | Return the unique (closed) inhabitant if exists.
--   In case of counting irrelevance in, the returned inhabitant
--   contains garbage.
isSingletonRecord' :: Bool -> QName -> Args -> TCM (Either MetaId (Maybe Term))
isSingletonRecord' regardIrrelevance r ps = do
  def <- getRecordDef r
  emap (Con $ recCon def) <$> check (recTel def `apply` ps)
  where
  check :: Telescope -> TCM (Either MetaId (Maybe [Arg Term]))
  check EmptyTel            = return $ Right $ Just []
  check (ExtendTel arg@(Dom h Irrelevant _) tel) | regardIrrelevance =
    underAbstraction arg tel $ \ tel ->
      emap (Arg h Irrelevant garbage :) <$> check tel
  check (ExtendTel arg@(Dom h r t) tel) = do
    isSing <- isSingletonType' regardIrrelevance t
    case isSing of
      Left mid       -> return $ Left mid
      Right Nothing  -> return $ Right Nothing
      Right (Just v) -> underAbstraction arg tel $ \ tel ->
        emap (Arg h r v :) <$> check tel
{- UNNECESSARILY UNREADABLE:
  check (ExtendTel arg tel) | regardIrrelevance && domRelevance arg == Irrelevant =
    underAbstraction arg tel $ \ tel ->
      emap (argFromDom (fmap (const garbage) arg) :) <$> check tel
  check (ExtendTel arg tel) = do
    isSing <- isSingletonType' regardIrrelevance (unDom arg)
    case isSing of
      Left mid       -> return $ Left mid
      Right Nothing  -> return $ Right Nothing
      Right (Just v) -> underAbstraction arg tel $ \ tel ->
        emap (argFromDom (fmap (const v) arg) :) <$> check tel
-}
  garbage :: Term
  garbage = Sort Prop

-- | Check whether a type has a unique inhabitant and return it.
--   Can be blocked by a metavar.
isSingletonType :: Type -> TCM (Either MetaId (Maybe Term))
isSingletonType = isSingletonType' False

-- | Check whether a type has a unique inhabitant (irrelevant parts ignored).
--   Can be blocked by a metavar.
isSingletonTypeModuloRelevance :: (MonadTCM tcm) => Type -> tcm (Either MetaId Bool)
isSingletonTypeModuloRelevance t = liftTCM $ do
  mapRight isJust <$> isSingletonType' True t

isSingletonType' :: Bool -> Type -> TCM (Either MetaId (Maybe Term))
isSingletonType' regardIrrelevance t = do
    TelV tel t <- telView t
    t <- reduceB $ unEl t
    case t of
      Blocked m _            -> return (Left m)
      NotBlocked (MetaV m _) -> return (Left m)
      NotBlocked (Def r ps)  ->
        ifM (isNothing <$> isRecord r) (return $ Right Nothing) $ do
          emap (abstract tel) <$> isSingletonRecord' regardIrrelevance r ps
      _ -> return (Right Nothing)

-- | Auxiliary function.
emap :: (a -> b) -> Either c (Maybe a) -> Either c (Maybe b)
emap = mapRight . fmap
