{-# LANGUAGE CPP, TupleSections #-}

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
import qualified Agda.Syntax.Abstract as A
import Agda.Syntax.Abstract.Name
import Agda.Syntax.Internal as I
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
import qualified Agda.Utils.HashMap as HMap

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
--   does not refer to a record or the record is abstract.
getRecordDef :: QName -> TCM Defn
getRecordDef r = maybe err return =<< isRecord r
  where err = typeError $ ShouldBeRecordType (El Prop $ Def r [])

-- | Get the field names of a record.
getRecordFieldNames :: QName -> TCM [I.Arg C.Name]
getRecordFieldNames r =
  map (fmap (nameConcrete . qnameName)) . recFields <$> getRecordDef r

-- | Find all records with at least the given fields.
findPossibleRecords :: [C.Name] -> TCM [QName]
findPossibleRecords fields = do
  defs <- (HMap.union `on` sigDefinitions) <$> getSignature <*> getImportedSignature
  let possible def = case theDef def of
        Record{ recFields = fs } -> Set.isSubsetOf given inrecord
          where inrecord = Set.fromList $ map (nameConcrete . qnameName . unArg) fs
        _ -> False
  return [ defName d | d <- HMap.elems defs, possible d ]
  where
    given = Set.fromList fields

-- | Get the field types of a record.
getRecordFieldTypes :: QName -> TCM Telescope
getRecordFieldTypes r = recTel <$> getRecordDef r

-- | Get the field names belonging to a record type.
getRecordTypeFields :: Type -> TCM [I.Arg QName]
getRecordTypeFields t =
  case ignoreSharing $ unEl t of
    Def r _ -> do
      rDef <- theDef <$> getConstInfo r
      case rDef of
        Record { recFields = fields } -> return fields
        _ -> __IMPOSSIBLE__
    _ -> __IMPOSSIBLE__


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
isEtaRecord r = maybe False recEtaEquality <$> isRecord r

-- | Check if a name refers to a record which is not coinductive.  (Projections are then size-preserving)
isInductiveRecord :: QName -> TCM Bool
isInductiveRecord r = maybe False (\ d -> recInduction d == Inductive || not (recRecursive d)) <$> isRecord r

-- | Check if a type is an eta expandable record and return the record identifier and the parameters.
isEtaRecordType :: Type -> TCM (Maybe (QName, Args))
isEtaRecordType a = case ignoreSharing $ unEl a of
  Def d ps -> ifM (isEtaRecord d) (return $ Just (d, ps)) (return Nothing)
  _        -> return Nothing

-- | Check if a name refers to a record constructor.
--   If yes, return record definition.
isRecordConstructor :: QName -> TCM (Maybe (QName, Defn))
isRecordConstructor c = do
  def <- theDef <$> getConstInfo c
  case def of
    Constructor{ conData = r } -> fmap (r,) <$> isRecord r
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

-- | Mark record type as unguarded.
--   No eta-expansion.  Projections do not preserve guardedness.
unguardedRecord :: QName -> TCM ()
unguardedRecord q = modifySignature $ updateDefinition q $ updateTheDef $ updateRecord
  where updateRecord r@Record{} = r { recEtaEquality = False, recRecursive = True }
        updateRecord _          = __IMPOSSIBLE__

-- | Mark record type as recursive.
--   Projections do not preserve guardedness.
recursiveRecord :: QName -> TCM ()
recursiveRecord q = modifySignature $ updateDefinition q $ updateTheDef $ updateRecord
  where updateRecord r@Record{} = r { recRecursive = True }
        updateRecord _          = __IMPOSSIBLE__

{-| Compute the eta expansion of a record. The first argument should be
    the name of a record type. Given

    @record R : Set where x : A; y : B; .z : C@

    and @r : R@, @etaExpand R [] r@ is @[R.x r, R.y r, DontCare]@
-}
etaExpandRecord :: QName -> Args -> Term -> TCM (Telescope, Args)
etaExpandRecord r pars u = do
  Record{ recFields = xs, recTel = tel, recEtaEquality = eta } <- getRecordDef r
  unless eta __IMPOSSIBLE__ -- make sure we do not expand non-eta records
  let tel' = apply tel pars
  case ignoreSharing u of
    Con _ args -> return (tel', args)  -- Already expanded.
    _          -> do
      let xs' = map (fmap (\ x -> Def x [defaultArg u])) xs
      reportSDoc "tc.record.eta" 20 $ vcat
        [ text "eta expanding" <+> prettyTCM u <+> text ":" <+> prettyTCM r
        , nest 2 $ vcat
          [ text "tel' =" <+> prettyTCM tel'
          , text "args =" <+> prettyTCM xs'
          ]
        ]
      return (tel', xs')

-- | The fields should be eta contracted already.
--
--   We can eta constract if all fields @f = ...@ are irrelevant
--   or the corresponding projection @f = f v@ of the same value @v@,
--   but we need at least one relevant field to find the value @v@.
etaContractRecord :: QName -> QName -> Args -> TCM Term
etaContractRecord r c args = do
  Record{ recPars = npars, recFields = xs } <- getRecordDef r
  let check :: I.Arg Term -> I.Arg QName -> Maybe (Maybe Term)
      check a ax = do
      -- @a@ is the constructor argument, @ax@ the corr. record field name
        -- skip irrelevant record fields by returning DontCare
        case (getRelevance a, ignoreSharing $ unArg a) of
          (Irrelevant, _) -> Just Nothing
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
  check :: Telescope -> TCM (Either MetaId (Maybe [I.Arg Term]))
  check EmptyTel            = return $ Right $ Just []
  check (ExtendTel dom tel)
        | isIrrelevant dom && regardIrrelevance =
    underAbstraction dom tel $ \ tel ->
      emap (Arg (domInfo dom) garbage :) <$> check tel
  check (ExtendTel dom tel) = do
    isSing <- isSingletonType' regardIrrelevance $ unDom dom
    case isSing of
      Left mid       -> return $ Left mid
      Right Nothing  -> return $ Right Nothing
      Right (Just v) -> underAbstraction dom tel $ \ tel ->
        emap (Arg (domInfo dom) v :) <$> check tel
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
    case ignoreSharing <$> t of
      Blocked m _            -> return (Left m)
      NotBlocked (MetaV m _) -> return (Left m)
      NotBlocked (Def r ps)  ->
        ifM (isNothing <$> isRecord r) (return $ Right Nothing) $ do
          emap (abstract tel) <$> isSingletonRecord' regardIrrelevance r ps
      _ -> return (Right Nothing)

-- | Auxiliary function.
emap :: (a -> b) -> Either c (Maybe a) -> Either c (Maybe b)
emap = mapRight . fmap
