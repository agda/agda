{-# LANGUAGE CPP #-}

-- | Contains the state monad that the compiler works in and some functions
--   for tampering with the state.
module Agda.Compiler.UHC.CompileState
  ( CompileT
  , runCompileT
  , uhcError

  , addConMap

  , getCoreName
  , getCoreName1
  , getConstrInfo
--  , getConstrTag
--  , getConstrArity

  , getCurrentModule

  , constructorArity
  , replaceAt
  )
where

import Control.Applicative
import Control.Monad.State
import Data.List
import Data.Map(Map)
import qualified Data.Map as M
import Data.Maybe
import Data.Monoid
import Data.Set(Set)
import qualified Data.Set as S

import Agda.Compiler.UHC.AuxAST as AuxAST
import Agda.Compiler.UHC.ModuleInfo
import Agda.Interaction.Options
import Agda.Syntax.Internal
import Agda.Syntax.Concrete(TopLevelModuleName)
import Agda.Syntax.Common
import Agda.TypeChecking.Monad (MonadTCM, TCM, internalError, defType, theDef, getConstInfo, sigDefinitions, stImports, stPersistentOptions, stPersistentState)
import qualified Agda.TypeChecking.Monad as TM
import Agda.TypeChecking.Reduce
import Agda.Compiler.UHC.Naming

import qualified Agda.Utils.HashMap as HM
import Agda.Utils.Lens

#include "undefined.h"
import Agda.Utils.Impossible

-- | Stuff we need in our compiler
data CompileState = CompileState
    { curModule       :: ModuleName
    , moduleInterface :: AModuleInterface    -- ^ Contains the interface of all imported and the currently compiling module.
--    , compiledModules :: Map TopLevelModuleName (EInterface, Set FilePath)
--    , curModule       :: EInterface
--    , importedModules :: EInterface
--    , curFun          :: String
    } deriving Show

-- | Compiler monad
type CompileT = StateT CompileState

-- | The initial (empty) state
runCompileT :: Monad m
    => ModuleName   -- ^ The module to compile.
    -> [AModuleInfo] -- ^ Imported module info (non-transitive).
    -> NameMap      -- ^ NameMap for the current module (non-transitive).
    -> CompileT m a
    -> m (a, AModuleInfo)
runCompileT mod impMods nmMp comp = do
  (result, state') <- runStateT comp initial

  let modInfo = AModuleInfo
        { amiModule = mod
        , amiInterface = moduleInterface state'
        , amiCurNameMp = nmMp
        }

  return (result, modInfo) 
  where initial = CompileState
            { curModule     = mod
            , moduleInterface   = mappend
                (mempty { amifNameMp = nmMp})
                (mconcat $ map amiInterface impMods)
            }

addConMap :: Monad m => M.Map QName AConInfo -> CompileT m ()
addConMap conMp = addInterface (mempty { amifConMp = conMp })

-- | Adds the given interface.
addInterface :: Monad m => AModuleInterface -> CompileT m ()
addInterface iface = modifyInterface (mappend iface)

modifyInterface :: Monad m => (AModuleInterface -> AModuleInterface) -> CompileT m ()
modifyInterface f = modify (\s -> s { moduleInterface = f (moduleInterface s )})



-- | When normal errors are not enough
uhcError :: MonadTCM m => String -> CompileT m a
uhcError = lift . internalError
{-
-- | Modify the state of the current module's Epic Interface
modifyEI :: MonadTCM m => (EInterface -> EInterface) -> Compile m ()
modifyEI f = modify $ \s -> s {curModule = f (curModule s)}

-- | Get the state of the current module's Epic Interface
getsEI :: MonadTCM m => (EInterface -> a) -> Compile m a
getsEI f = gets (f . curModule)

-- | Returns the type of a definition given its name
getType :: MonadTCM m => QName -> Compile m Type
getType q = do
    map <- lift (sigDefinitions <$> use stImports)
    return $ maybe __IMPOSSIBLE__ defType (HM.lookup q map)
-}

getCoreName :: Monad m => QName -> CompileT m (Maybe HsName)
getCoreName qnm = do
  nmMp <- gets (amifNameMp . moduleInterface)
  return $ (cnName <$> qnameToCoreName nmMp qnm)

getCoreName1 :: Monad m => QName -> CompileT m HsName
getCoreName1 nm = getCoreName nm >>= return . fromJust

getConstrInfo :: (Functor m, Monad m) => QName -> CompileT m AConInfo
getConstrInfo n = M.findWithDefault __IMPOSSIBLE__ n <$> gets (amifConMp . moduleInterface)

{-getConstrTag :: MonadTCM m => QName -> CompileT m Tag
getConstrTag n = xconTag . aciDataCon <$> getConstrInfo n

getConstrArity :: MonadTCM m => QName -> CompileT m Int
getConstrArity n = xconArity . aciDataCon <$> getConstrInfo n-}

getCurrentModule :: Monad m => CompileT m ModuleName
getCurrentModule = gets curModule

-- * State modifiers
{-getDelayed :: MonadTCM m => QName -> Compile m Bool
getDelayed q = lookInterface (M.lookup q . defDelayed) (return False)

putDelayed :: MonadTCM m => QName -> Bool -> Compile m ()
putDelayed q d = modifyEI $ \s -> s {defDelayed = M.insert q d (defDelayed s)}

putConstrTag :: MonadTCM m => QName -> Tag -> Compile m ()
putConstrTag q t = modifyEI $ \s -> s { constrTags = M.insert q t $ constrTags s }

assignConstrTag :: MonadTCM m => QName -> Compile m Tag
assignConstrTag constr = assignConstrTag' constr []

assignConstrTag' :: MonadTCM m => QName -> [QName] -> Compile m Tag
assignConstrTag' constr constrs = do
    constrs <- concat <$> mapM ((getDataCon =<<) . getConData) (constr : constrs)
    tags    <- catMaybes <$> mapM getConstrTag' constrs
    let tag =  head $ [0..] \\ tags
    putConstrTag constr tag
    return tag

getConData :: MonadTCM m => QName -> Compile m QName
getConData con = do
    lmap <- lift (TM.sigDefinitions <$> use TM.stImports)
    case HM.lookup con lmap of
        Just def -> case theDef def of
            c@(TM.Constructor{}) -> return $ TM.conData c
            _                 -> __IMPOSSIBLE__
        Nothing -> __IMPOSSIBLE__

getDataCon :: MonadTCM m => QName -> Compile m [QName]
getDataCon con = do
    lmap <- lift (TM.sigDefinitions <$> use TM.stImports)
    case HM.lookup con lmap of
        Just def -> case theDef def of
            d@(TM.Datatype{}) -> return $ TM.dataCons d
            r@(TM.Record{})   -> return [ TM.recCon r]
            _                 -> __IMPOSSIBLE__
        Nothing -> __IMPOSSIBLE__

getConstrTag :: MonadTCM m => QName -> Compile m Tag
getConstrTag con = lookInterface (M.lookup con . constrTags)
                                 (assignConstrTag con)

getConstrTag' :: MonadTCM m => QName -> Compile m (Maybe Tag)
getConstrTag' con = do
    cur <- gets curModule
    case M.lookup con (constrTags cur) of
        Just x -> return (Just x)
        Nothing -> do
            imps <- gets importedModules
            return $ M.lookup con (constrTags imps)-}

{-addDefName :: MonadTCM m => QName -> Compile m ()
addDefName q = do
    modifyEI $ \s -> s {definitions = S.insert (unqname q) $ definitions s }-}

{-topBindings :: MonadTCM m => Compile m (Set HsName)
topBindings = S.union <$> gets (definitions . importedModules) <*> gets (definitions . curModule)

getConArity :: MonadTCM m => QName -> Compile m Int
getConArity n = lookInterface (M.lookup n . conArity) __IMPOSSIBLE__

putConArity :: MonadTCM m => QName -> Int -> Compile m ()
putConArity n p = modifyEI $ \s -> s { conArity = M.insert n p (conArity s) }

putMain :: MonadTCM m => QName -> Compile m ()
putMain m = modifyEI $ \s -> s { mainName = Just m }-}

--getMain :: MonadTCM m => Compile m HsName
--getMain = maybe (epicError "Where is main? :(") (return . unqname) =<< getsEI mainName

{-
lookInterface :: MonadTCM m => (EInterface -> Maybe a) -> Compile m a -> Compile m a
lookInterface f def = do
    cur <- gets curModule
    case f cur of
        Just x -> return x
        Nothing -> do
            imps <- gets importedModules
            case f imps of
                Nothing -> def
                Just x  -> return x

constrInScope :: MonadTCM m => QName -> Compile m Bool
constrInScope name = do
    cur <- gets curModule
    case M.lookup name (constrTags cur) of
        Just x -> return True
        Nothing -> do
            imps <- gets importedModules
            case M.lookup name (constrTags imps) of
                Nothing -> return False
                Just x  -> return True

getForcedArgs :: MonadTCM m => QName -> Compile m ForcedArgs
getForcedArgs q = lookInterface (M.lookup q . forcedArgs) __IMPOSSIBLE__

putForcedArgs :: MonadTCM m => QName -> ForcedArgs -> Compile m ()
putForcedArgs n f = do
  b <- lift $ gets (optForcing . stPersistentOptions . stPersistentState)
  let f' | b = f
         | otherwise = replicate (length f) NotForced
  modifyEI $ \s -> s {forcedArgs = M.insert n f' $ forcedArgs s}
-}
-- TODO What does this have to do with CompileState? Move
replaceAt :: Int -- ^ replace at
          -> [a] -- ^ to replace
          -> [a] -- ^ replace with
          -> [a] -- ^ result?
replaceAt n xs inserts = let (as, _:bs) = splitAt n xs in as ++ inserts ++ bs


-- TODO this has nothing todo with the CompileState.., move
-- | Copy pasted from MAlonzo, then Epic, HAHA!!!
--   Move somewhere else!
constructorArity :: Num a => QName -> TCM a
constructorArity q = do
  def <- getConstInfo q
  a <- normalise $ defType def
  case theDef def of
    TM.Constructor{ TM.conPars = np } -> return . fromIntegral $ arity a - np
    _ -> internalError $ "constructorArity: non constructor: " ++ show q

