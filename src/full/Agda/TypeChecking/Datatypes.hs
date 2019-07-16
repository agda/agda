
module Agda.TypeChecking.Datatypes where

import Control.Monad.Except

import Data.Maybe (fromMaybe)
import qualified Data.List as List

import Agda.Syntax.Common
import Agda.Syntax.Internal

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Monad.Builtin (constructorForm)
import Agda.TypeChecking.Telescope
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Pretty

import Agda.Utils.Either
import Agda.Utils.Pretty ( prettyShow )
import Agda.Utils.Size

import Agda.Utils.Impossible

---------------------------------------------------------------------------
-- * Constructors
---------------------------------------------------------------------------

-- | Get true constructor with record fields.
getConHead :: (HasConstInfo m) => QName -> m (Either SigError ConHead)
getConHead c = runExceptT $ do
  def <- ExceptT $ getConstInfo' c
  case theDef def of
    Constructor { conSrcCon = c' } -> return c'
    Record     { recConHead = c' } -> return c'
    _ -> throwError $ SigUnknown $ prettyShow c ++ " is not a constructor"

-- | Get true constructor with fields, expanding literals to constructors
--   if possible.
getConForm :: QName -> TCM (Either SigError ConHead)
getConForm c = caseEitherM (getConHead c) (return . Left) $ \ ch -> do
  Con con _ [] <- constructorForm (Con ch ConOCon [])
  return $ Right con

-- | Augment constructor with record fields (preserve constructor name).
--   The true constructor might only surface via 'reduce'.
getOrigConHead :: QName -> TCM (Either SigError ConHead)
getOrigConHead c = mapRight (setConName c) <$> getConHead c

-- | Get the name of the datatype constructed by a given constructor.
--   Precondition: The argument must refer to a constructor
{-# SPECIALIZE getConstructorData :: QName -> TCM QName #-}
getConstructorData :: HasConstInfo m => QName -> m QName
getConstructorData c = do
  def <- getConstInfo c
  case theDef def of
    Constructor{conData = d} -> return d
    _                        -> __IMPOSSIBLE__

-- | Is the datatype of this constructor a Higher Inductive Type?
--   Precondition: The argument must refer to a constructor of a datatype or record.
consOfHIT :: QName -> TCM Bool
consOfHIT c = do
  d <- getConstructorData c
  def <- theDef <$> getConstInfo d
  case def of
    Datatype {dataPathCons = xs} -> return $ not $ null xs
    Record{} -> return False
    _  -> __IMPOSSIBLE__

-- | @getConType c t@ computes the constructor parameters from type @t@
--   and returns them plus the instantiated type of constructor @c@.
--   This works also if @t@ is a function type ending in a data/record type;
--   the term from which @c@ comes need not be fully applied
--
--   @Nothing@ if @t@ is not a data/record type or does not have
--   a constructor @c@.
getConType
  :: (MonadReduce m, MonadAddContext m, HasConstInfo m, MonadDebug m)
  => ConHead  -- ^ Constructor.
  -> Type     -- ^ Ending in data/record type.
  -> m (Maybe ((QName, Type, Args), Type))
       -- ^ @Nothing@ if not ends in data or record type.
       --
       --   @Just ((d, dt, pars), ct)@ otherwise, where
       --     @d@    is the data or record type name,
       --     @dt@   is the type of the data or record name,
       --     @pars@ are the reconstructed parameters,
       --     @ct@   is the type of the constructor instantiated to the parameters.
getConType c t = do
  reportSDoc "tc.getConType" 30 $ sep $
    [ "getConType: constructor "
    , prettyTCM c
    , " at type "
    , prettyTCM t
    ]
  TelV tel t <- telView t
  -- Now @t@ lives under @tel@, we need to remove the dependency on @tel@.
  -- This will succeed if @t@ is indeed a data/record type that is the
  -- type of a constructor coming from a term
  -- (applied to at least the parameters).
  -- Note: @t@ will have some unbound deBruijn indices if view outside of @tel@.
  reportSLn "tc.getConType" 35 $ "  target type: " ++ prettyShow t
  applySubst (strengthenS __IMPOSSIBLE__ (size tel)) <$> do
    addContext tel $ getFullyAppliedConType c t
  -- Andreas, 2017-08-18, issue #2703:
  -- The original code
  --    getFullyAppliedConType c $ applySubst (strengthenS __IMPOSSIBLE__ (size tel)) t
  -- crashes because substitution into @Def@s is slightly too strict
  -- (see @defApp@ and @canProject@).
  -- Strengthening the parameters after the call to @getFullyAppliedConType@
  -- does not produce intermediate terms with __IMPOSSIBLE__s and this thus
  -- robust wrt. strictness/laziness of substitution.

-- | @getFullyAppliedConType c t@ computes the constructor parameters
--   from data type @t@ and returns them
--   plus the instantiated type of constructor @c@.
--
--   @Nothing@ if @t@ is not a data/record type or does not have
--   a constructor @c@.
--
--   Precondition: @t@ is reduced.
getFullyAppliedConType
  :: (HasConstInfo m, MonadReduce m, MonadDebug m)
  => ConHead  -- ^ Constructor.
  -> Type     -- ^ Reduced type of the fully applied constructor.
  -> m (Maybe ((QName, Type, Args), Type))
       -- ^ @Nothing@ if not data or record type.
       --
       --   @Just ((d, dt, pars), ct)@ otherwise, where
       --     @d@    is the data or record type name,
       --     @dt@   is the type of the data or record name,
       --     @pars@ are the reconstructed parameters,
       --     @ct@   is the type of the constructor instantiated to the parameters.
getFullyAppliedConType c t = do
  reportSLn "tc.getConType" 35 $ List.intercalate " " $
    [ "getFullyAppliedConType", prettyShow c, prettyShow t ]
  c <- fromRight __IMPOSSIBLE__ <$> do getConHead $ conName c
  case unEl t of
    -- Note that if we come e.g. from getConType,
    -- then the non-parameter arguments of @es@ might contain __IMPOSSIBLE__
    -- coming from strengthening.  (Thus, printing them is not safe.)
    Def d es -> do
      reportSLn "tc.getConType" 35 $ List.intercalate " " $
        [ "getFullyAppliedConType: case Def", prettyShow d, prettyShow es ]
      def <- getConstInfo d
      let cont n = do
            -- At this point we can be sure that the parameters are well-scoped.
            let pars = fromMaybe __IMPOSSIBLE__ $ allApplyElims $ take n es
            Just . ((d, defType def, pars),) <$> do
              (`piApplyM` pars) . defType =<< getConInfo c
      case theDef def of
        Datatype { dataPars = n, dataCons   = cs  } | conName c `elem` cs -> cont n
        Record   { recPars  = n, recConHead = con } | c == con            -> cont n
        _ ->  return Nothing
    _ -> return Nothing

data ConstructorInfo
  = DataCon Nat                  -- ^ Arity.
  | RecordCon HasEta [Arg QName] -- ^ List of field names.

-- | Return the number of non-parameter arguments to a data constructor,
--   or the field names of a record constructor.
--
--   For getting just the arity of constructor @c@,
--   use @either id size <$> getConstructorArity c@.
getConstructorInfo :: QName -> TCM ConstructorInfo
getConstructorInfo c = do
  (theDef <$> getConstInfo c) >>= \case
    Constructor{ conData = d, conArity = n } -> do
      (theDef <$> getConstInfo d) >>= \case
        r@Record{ recFields = fs } ->
           return $ RecordCon (recEtaEquality r) fs
        Datatype{} ->
           return $ DataCon n
        _ -> __IMPOSSIBLE__
    _ -> __IMPOSSIBLE__

---------------------------------------------------------------------------
-- * Data types
---------------------------------------------------------------------------

-- | Check if a name refers to a datatype or a record with a named constructor.
isDatatype :: QName -> TCM Bool
isDatatype d = do
  def <- getConstInfo d
  case theDef def of
    Datatype{}                   -> return True
    Record{recNamedCon = namedC} -> return namedC
    _                            -> return False

-- | Check if a name refers to a datatype or a record.
isDataOrRecordType :: QName -> TCM (Maybe DataOrRecord)
isDataOrRecordType d = do
  def <- getConstInfo d
  case theDef def of
    Datatype{} -> return $ Just IsData
    Record{}   -> return $ Just IsRecord
    _          -> return $ Nothing

-- | Precodition: 'Term' is 'reduce'd.
isDataOrRecord :: Term -> TCM (Maybe QName)
isDataOrRecord v = do
  case v of
    Def d _ -> fmap (const d) <$> isDataOrRecordType d
    _       -> return Nothing

getNumberOfParameters :: QName -> TCM (Maybe Nat)
getNumberOfParameters d = do
  def <- getConstInfo d
  case theDef def of
    Datatype{ dataPars = n }   -> return $ Just n
    Record{ recPars = n }      -> return $ Just n
    Constructor{ conPars = n } -> return $ Just n
    _                          -> return Nothing

-- | Precondition: Name is a data or record type.
getConstructors :: QName -> TCM [QName]
getConstructors d = fromMaybe __IMPOSSIBLE__ <$>
  getConstructors' d

-- | 'Nothing' if not data or record type name.
getConstructors' :: QName -> TCM (Maybe [QName])
getConstructors' d = getConstructors_ . theDef <$> getConstInfo d

-- | 'Nothing' if not data or record definition.
getConstructors_ :: Defn -> Maybe [QName]
getConstructors_ = \case
    Datatype{dataCons = cs} -> Just cs
    Record{recConHead = h}  -> Just [conName h]
    _                       -> Nothing

-- | Precondition: Name is a data or record type.
getConHeads :: QName -> TCM [ConHead]
getConHeads d = fromMaybe __IMPOSSIBLE__ <$>
  getConHeads' d

-- | 'Nothing' if not data or record type name.
getConHeads' :: QName -> TCM (Maybe [ConHead])
getConHeads' d = getConHeads_ . theDef <$> getConstInfo d

-- | 'Nothing' if not data or record definition.
getConHeads_ :: Defn -> Maybe [ConHead]
getConHeads_ = \case
    Datatype{dataCons = cs} -> Just $ map (\ c -> ConHead c Inductive []) cs
    Record{recConHead = h}  -> Just [h]
    _                       -> Nothing

{- UNUSED
data DatatypeInfo = DataInfo
  { datatypeName   :: QName
  , datatypeParTel :: Telescope
  , datatypePars   :: Args
  , datatypeIxTel  :: Telescope
  , datatypeIxs    :: Args
  }

-- | Get the name and parameters from a type if it's a datatype or record type
--   with a named constructor.
getDatatypeInfo :: Type -> TCM (Maybe DatatypeInfo)
getDatatypeInfo t = do
  t <- reduce t
  case unEl t of
    Def d args -> do
      n          <- getDefFreeVars d
      args       <- return $ genericDrop n args
      def        <- instantiateDef =<< getConstInfo d
      TelV tel _ <- telView (defType def)
      let npars  = case theDef def of
            Datatype{dataPars = np} -> Just np
            Record{recPars = np, recNamedCon = True}
              | genericLength args == np -> Just np
              | otherwise                -> __IMPOSSIBLE__
            _                            -> Nothing
      return $ do
        np <- npars
        let (pt, it) = genericSplitAt np $ telToList tel
            parTel   = telFromList pt
            ixTel    = telFromList it
            (ps, is) = genericSplitAt np args
        return $ DataInfo { datatypeName = d
                          , datatypeParTel = parTel
                          , datatypePars   = ps
                          , datatypeIxTel  = ixTel
                          , datatypeIxs    = is
                          }
    _ -> return Nothing
-}
