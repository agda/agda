
module Agda.TypeChecking.Datatypes where

import Control.Monad        ( filterM )
import Control.Monad.Except ( MonadError(..), ExceptT(..), runExceptT )

import Data.Maybe (fromMaybe)

import Agda.Syntax.Common
import Agda.Syntax.Internal

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Telescope
import Agda.TypeChecking.Reduce
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

isConstructor :: (HasConstInfo m) => QName -> m Bool
isConstructor q = isRight <$> getConHead q

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
consOfHIT :: HasConstInfo m => QName -> m Bool
consOfHIT c = do
  d <- getConstructorData c
  def <- theDef <$> getConstInfo d
  case def of
    Datatype {dataPathCons = xs} -> return $ not $ null xs
    Record{} -> return False
    _  -> __IMPOSSIBLE__

isPathCons :: HasConstInfo m => QName -> m Bool
isPathCons c = do
  d <- getConstructorData c
  def <- theDef <$> getConstInfo d
  case def of
    Datatype {dataPathCons = xs} -> return $ c `elem` xs
    Record{} -> return False
    _  -> __IMPOSSIBLE__

-- | @getFullyAppliedConType c t@ computes the constructor parameters
--   from data type @t@ and returns them
--   plus the instantiated type of constructor @c@.
--
--   @Nothing@ if @t@ is not a data/record type or does not have
--   a constructor @c@.
--
--   Precondition: @t@ is reduced.
getFullyAppliedConType
  :: PureTCM m
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
  reportSLn "tc.getConType" 35 $ unwords $
    [ "getFullyAppliedConType", prettyShow c, prettyShow t ]
  c <- fromRight __IMPOSSIBLE__ <$> getConHead (conName c)
  cdef <- getConstInfo $ conName c
  let ctype = defType cdef
      cdata = conData $ theDef cdef
      npars = conPars $ theDef cdef
  case unEl t of
    Def d es | d == cdata -> do
      reportSLn "tc.getConType" 35 $ unwords $
        [ "getFullyAppliedConType: case Def", prettyShow d, prettyShow es ]
      dt <- defType <$> getConstInfo d
      let pars = fromMaybe __IMPOSSIBLE__ $ allApplyElims $ take npars es
      ctPars <- ctype `piApplyM` pars
      return $ Just ((d, dt, pars), ctPars)
    _ -> return Nothing

-- | Make sure a constructor is fully applied and infer the type of the constructor.
--   Raises a type error if the constructor does not belong to the given type.
fullyApplyCon
  :: (PureTCM m, MonadBlock m, MonadTCError m)
  => ConHead -- ^ Constructor.
  -> Elims    -- ^ Constructor arguments.
  -> Type    -- ^ Type of the constructor application.
  -> (QName -> Type -> Args -> Type -> Elims -> Telescope -> Type -> m a)
       -- ^ Name of the data/record type,
       --   type of the data/record type,
       --   reconstructed parameters,
       --   type of the constructor (applied to parameters),
       --   full application arguments,
       --   types of missing arguments (already added to context),
       --   type of the full application.
  -> m a
fullyApplyCon c vs t ret = fullyApplyCon' c vs t ret $
  typeError . DoesNotConstructAnElementOf (conName c)

-- | Like @fullyApplyCon@, but calls the given fallback function if
--   it encounters something other than a datatype.
fullyApplyCon'
  :: (PureTCM m, MonadBlock m)
  => ConHead -- ^ Constructor.
  -> Elims    -- ^ Constructor arguments.
  -> Type    -- ^ Type of the constructor application.
  -> (QName -> Type -> Args -> Type -> Elims -> Telescope -> Type -> m a) -- ^ See @fullyApplyCon@
  -> (Type -> m a) -- ^ Fallback function
  -> m a
fullyApplyCon' c vs t0 ret err = do
  reportSDoc "tc.getConType" 30 $ sep $
    [ "fullyApplyCon': constructor "
    , prettyTCM c
    , " with arguments"
    , prettyTCM vs
    , " at type "
    , prettyTCM t0
    ]
  (TelV tel t, boundary) <- telViewPathBoundaryP t0
  -- The type of the constructor application may still be a function
  -- type.  In this case, we introduce the domains @tel@ into the context
  -- and apply the constructor to these fresh variables.
  addContext tel $ do
    reportSLn "tc.getConType" 35 $ "  target type: " ++ prettyShow t
    t <- abortIfBlocked t
    getFullyAppliedConType c t >>= \case
      Nothing -> err t
      Just ((d, dt, pars), a) ->
        ret d dt pars a (raise (size tel) vs ++ teleElims tel boundary) tel t

-- | @getConType c t@ computes the constructor parameters from type @t@
--   and returns them plus the instantiated type of constructor @c@.
--   This works also if @t@ is a function type ending in a data/record type;
--   the term from which @c@ comes need not be fully applied
--
--   @Nothing@ if @t@ is not a data/record type or does not have
--   a constructor @c@.
getConType
  :: (PureTCM m, MonadBlock m)
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
getConType ch t = do
  let c = conName ch
  -- Optimization: if the constructor has no parameters, there
  -- is no need to reduce the type.
  npars <- getNumberOfParameters c
  if | npars == Just 0 -> do
      ctype <- defType <$> getConstInfo c
      d  <- getConstructorData c
      dtype <- defType <$> getConstInfo d
      return $ Just ((d,dtype,[]),ctype)
     | otherwise -> fullyApplyCon' ch [] t
      (\d dt pars ct es tel a -> return $
        -- Now @dt@, @pars@, and @ct@ live under @tel@,
        -- so we need to remove the dependency on @tel@.
        let escape = applySubst (strengthenS impossible (size tel)) in
        Just $ escape ((d, dt, pars), ct))
      (\_ -> return Nothing)

data ConstructorInfo
  = DataCon Arity
      -- ^ Arity of the data constructor.
  | RecordCon PatternOrCopattern HasEta
      Arity
      -- ^ Arity of the record constructor.
      [Dom QName]
      -- ^ List of field names. Has length 'Arity'.

-- | Return the number of non-parameter arguments to a constructor (arity).
--   In case of record constructors, also return the field names (plus other info).
--
getConstructorInfo :: HasConstInfo m => QName -> m ConstructorInfo
getConstructorInfo c = fromMaybe __IMPOSSIBLE__ <$> getConstructorInfo' c

getConstructorInfo' :: HasConstInfo m => QName -> m (Maybe ConstructorInfo)
getConstructorInfo' c = do
  (theDef <$> getConstInfo c) >>= \case
    Constructor{ conData = d, conArity = n } -> Just <$> do
      (theDef <$> getConstInfo d) >>= \case
        r@Record{ recFields = fs } ->
           return $ RecordCon (recPatternMatching r) (recEtaEquality r) n fs
        Datatype{} ->
           return $ DataCon n
        _ -> __IMPOSSIBLE__
    _ -> return Nothing

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
  (theDef <$> getConstInfo d) >>= \case
    Record{ recPatternMatching } -> return $ Just $ IsRecord recPatternMatching
    Datatype{} -> return $ Just IsData
    _          -> return $ Nothing

-- | Precodition: 'Term' is 'reduce'd.
isDataOrRecord :: Term -> TCM (Maybe QName)
isDataOrRecord = \case
    Def d _ -> fmap (const d) <$> isDataOrRecordType d
    _       -> return Nothing

getNumberOfParameters :: HasConstInfo m => QName -> m (Maybe Nat)
getNumberOfParameters d = do
  def <- getConstInfo d
  case theDef def of
    Datatype{ dataPars = n }   -> return $ Just n
    Record{ recPars = n }      -> return $ Just n
    Constructor{ conPars = n } -> return $ Just n
    _                          -> return Nothing

-- | This is a simplified version of @isDatatype@ from @Coverage@,
--   useful when we do not want to import the module.
getDatatypeArgs :: HasConstInfo m => Type -> m (Maybe (QName, Args, Args))
getDatatypeArgs t = do
  case unEl t of
    Def d es -> do
      let ~(Just args) = allApplyElims es
      def <- theDef <$> getConstInfo d
      case def of
        Datatype{dataPars = np} -> do
          let !(ps, is) = splitAt np args
          return $ Just (d,   ps, is)
        Record{} -> do
          return $ Just (d, args, [])
        _ -> return Nothing
    _ -> return Nothing

getNotErasedConstructors :: QName -> TCM [QName]
getNotErasedConstructors d = do
  cs <- getConstructors d
  flip filterM cs $ \ c -> do
    usableModality <$> getConstInfo c

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
