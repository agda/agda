{-# LANGUAGE CPP #-}

-- | Contains the state monad that the compiler works in and some functions
--   for tampering with the state.
module Agda.Compiler.UHC.CompileState where

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
import Agda.Compiler.UHC.Interface
import Agda.Interaction.Options
import Agda.Syntax.Internal
import Agda.Syntax.Concrete(TopLevelModuleName)
import Agda.Syntax.Common
import Agda.TypeChecking.Monad (MonadTCM, TCM, internalError, defType, theDef, getConstInfo, sigDefinitions, stImports, stPersistentOptions, stPersistent)
import qualified Agda.TypeChecking.Monad as TM
import Agda.TypeChecking.Reduce

import qualified Agda.Utils.HashMap as HM

#include "../../undefined.h"
import Agda.Utils.Impossible

-- | Stuff we need in our compiler
data CompileState = CompileState
    { nameSupply      :: [AName]
    , compiledModules :: Map TopLevelModuleName (EInterface, Set FilePath)
    , curModule       :: EInterface
    , importedModules :: EInterface
    , curFun          :: String
    } deriving Show

-- | The initial (empty) state
initCompileState :: CompileState
initCompileState = CompileState
    { nameSupply        = map (ANmAgda . ('h':) . show) [0 :: Integer ..]
    , compiledModules   = M.empty
    , curModule         = mempty
    , importedModules   = mempty
    , curFun            = undefined
    }

-- | Compiler monad
type Compile = StateT CompileState

-- | When normal errors are not enough
epicError :: MonadTCM m => String -> Compile m a
epicError = lift . internalError

-- | Modify the state of the current module's Epic Interface
modifyEI :: MonadTCM m => (EInterface -> EInterface) -> Compile m ()
modifyEI f = modify $ \s -> s {curModule = f (curModule s)}

-- | Get the state of the current module's Epic Interface
getsEI :: MonadTCM m => (EInterface -> a) -> Compile m a
getsEI f = gets (f . curModule)

-- | Returns the type of a definition given its name
getType :: MonadTCM m => QName -> Compile m Type
getType q = do
    map <- lift (gets (sigDefinitions . stImports))
    return $ maybe __IMPOSSIBLE__ defType (HM.lookup q map)

-- | Create a name which can be used in Epic code from a QName.
unqname :: QName -> AName
unqname qn = ANmAgda $ show qn
--case nameId $ qnameName qn of
--    NameId name modul -> 'd' : show modul
--                     ++ "_" ++ show name

-- * State modifiers

resetNameSupply :: MonadTCM m => Compile m ()
resetNameSupply = modify $ \s -> s {nameSupply = nameSupply initCompileState}

getDelayed :: MonadTCM m => QName -> Compile m Bool
getDelayed q = lookInterface (M.lookup q . defDelayed) (return False)

putDelayed :: MonadTCM m => QName -> Bool -> Compile m ()
putDelayed q d = modifyEI $ \s -> s {defDelayed = M.insert q d (defDelayed s)}

newName :: MonadTCM m => Compile m AName
newName = do
    n:ns <- gets nameSupply
    modify $ \s -> s { nameSupply = ns}
    return n

-- | Derives a new unique (agda) name from the given name.
newName1 :: MonadTCM m => AName -> Compile m AName
newName1 np = do
  n' <- newName
  return $ ANmAgda (aNmName np ++ "_" ++ aNmName n')

putConstrTag :: MonadTCM m => QName -> Tag -> Compile m ()
putConstrTag q t = modifyEI $ \s -> s { constrTags = M.insert q t $ constrTags s }

assignConstrTag :: MonadTCM m => QName -> Compile m Tag
assignConstrTag constr = assignConstrTag' constr []

assignConstrTag' :: MonadTCM m => QName -> [QName] -> Compile m Tag
assignConstrTag' constr constrs = do
    constrs <- concat <$> mapM ((getDataCon =<<) . getConData) (constr : constrs)
    tags    <- catMaybes <$> mapM getConstrTag' constrs
    let tag =  head $ map Tag [0..] \\ tags
    putConstrTag constr tag
    return tag

getConData :: MonadTCM m => QName -> Compile m QName
getConData con = do
    lmap <- lift (gets (TM.sigDefinitions . TM.stImports))
    case HM.lookup con lmap of
        Just def -> case theDef def of
            c@(TM.Constructor{}) -> return $ TM.conData c
            _                 -> __IMPOSSIBLE__
        Nothing -> __IMPOSSIBLE__

getDataCon :: MonadTCM m => QName -> Compile m [QName]
getDataCon con = do
    lmap <- lift (gets (TM.sigDefinitions . TM.stImports))
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
            return $ M.lookup con (constrTags imps)

addDefName :: MonadTCM m => QName -> Compile m ()
addDefName q = do
    modifyEI $ \s -> s {definitions = S.insert (unqname q) $ definitions s }

topBindings :: MonadTCM m => Compile m (Set AName)
topBindings = S.union <$> gets (definitions . importedModules) <*> gets (definitions . curModule)

getConArity :: MonadTCM m => QName -> Compile m Int
getConArity n = lookInterface (M.lookup n . conArity) __IMPOSSIBLE__

putConArity :: MonadTCM m => QName -> Int -> Compile m ()
putConArity n p = modifyEI $ \s -> s { conArity = M.insert n p (conArity s) }

putMain :: MonadTCM m => QName -> Compile m ()
putMain m = modifyEI $ \s -> s { mainName = Just m }

getMain :: MonadTCM m => Compile m AName
getMain = maybe (epicError "Where is main? :(") (return . unqname) =<< getsEI mainName

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
  b <- lift $ gets (optForcing . stPersistentOptions . stPersistent)
  let f' | b = f
         | otherwise = replicate (length f) NotForced
  modifyEI $ \s -> s {forcedArgs = M.insert n f' $ forcedArgs s}

replaceAt :: Int -- ^ replace at
          -> [a] -- ^ to replace
          -> [a] -- ^ replace with
          -> [a] -- ^ result?
replaceAt n xs inserts = let (as, _:bs) = splitAt n xs in as ++ inserts ++ bs

-- | Copy pasted from MAlonzo, HAHA!!!
--   Move somewhere else!
constructorArity :: Num a => QName -> TCM a
constructorArity q = do
  def <- getConstInfo q
  a <- normalise $ defType def
  case theDef def of
    TM.Constructor{ TM.conPars = np } -> return . fromIntegral $ arity a - np
    _ -> internalError $ "constructorArity: non constructor: " ++ show q

-- | Bind an expression to a fresh variable name
bindExpr :: MonadTCM m => Expr -> (AName -> Compile m Expr) -> Compile m Expr
bindExpr expr f = case expr of
  AuxAST.Var v -> f v
  _     -> do
      v <- newName
      lett v expr <$> f v
