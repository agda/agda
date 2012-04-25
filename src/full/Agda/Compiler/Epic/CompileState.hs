{-# LANGUAGE CPP #-}

-- | Contains the state monad that the compiler works in and some functions
--   for tampering with the state.
module Agda.Compiler.Epic.CompileState where

import Control.Applicative
import Control.Monad.State
import Data.List
import Data.Map(Map)
import qualified Data.Map as M
import Data.Maybe
import Data.Monoid
import Data.Set(Set)
import qualified Data.Set as S

import Agda.Compiler.Epic.AuxAST as AuxAST
import Agda.Compiler.Epic.Interface
import Agda.Interaction.Options
import Agda.Syntax.Internal
import Agda.Syntax.Concrete(TopLevelModuleName)
import Agda.Syntax.Common
import Agda.TypeChecking.Monad (TCM, internalError, defType, theDef, getConstInfo, sigDefinitions, stImports, stPersistentOptions, stPersistent)
import qualified Agda.TypeChecking.Monad as TM
import Agda.TypeChecking.Reduce

#include "../../undefined.h"
import Agda.Utils.Impossible
import Agda.Utils.Monad
import qualified Agda.Utils.HashMap as HM


-- | Stuff we need in our compiler
data CompileState = CompileState
    { nameSupply      :: [Var]
    , compiledModules :: Map TopLevelModuleName (EInterface, Set FilePath)
    , curModule       :: EInterface
    , importedModules :: EInterface
    , curFun          :: String
    } deriving Show

-- | The initial (empty) state
initCompileState :: CompileState
initCompileState = CompileState
    { nameSupply        = map (('h':) . show) [0 :: Integer ..]
    , compiledModules   = M.empty
    , curModule         = mempty
    , importedModules   = mempty
    , curFun            = undefined
    }

-- | Compiler monad
type Compile = StateT CompileState

-- | When normal errors are not enough
epicError :: String -> Compile TCM a
epicError = lift . internalError

-- | Modify the state of the current module's Epic Interface
modifyEI :: (EInterface -> EInterface) -> Compile TCM ()
modifyEI f = modify $ \s -> s {curModule = f (curModule s)}

-- | Get the state of the current module's Epic Interface
getsEI :: (EInterface -> a) -> Compile TCM a
getsEI f = gets (f . curModule)

-- | Returns the type of a definition given its name
getType :: QName -> Compile TCM Type
getType q = do
    map <- lift (gets (sigDefinitions . stImports))
    return $ maybe __IMPOSSIBLE__ defType (HM.lookup q map)

-- | Create a name which can be used in Epic code from a QName.
unqname :: QName -> Var
unqname qn = case nameId $ qnameName qn of
    NameId name modul -> 'd' : show modul
                     ++ "_" ++ show name

-- * State modifiers

resetNameSupply :: Compile TCM ()
resetNameSupply = modify $ \s -> s {nameSupply = nameSupply initCompileState}

getDelayed :: QName -> Compile TCM Bool
getDelayed q = lookInterface (M.lookup q . defDelayed) (return False)

putDelayed :: QName -> Bool -> Compile TCM ()
putDelayed q d = modifyEI $ \s -> s {defDelayed = M.insert q d (defDelayed s)}

newName :: Compile TCM Var
newName = do
    n:ns <- gets nameSupply
    modify $ \s -> s { nameSupply = ns}
    return n

putConstrTag :: QName -> Tag -> Compile TCM ()
putConstrTag q t = modifyEI $ \s -> s { constrTags = M.insert q t $ constrTags s }

assignConstrTag :: QName -> Compile TCM Tag
assignConstrTag constr = assignConstrTag' constr []

assignConstrTag' :: QName -> [QName] -> Compile TCM Tag
assignConstrTag' constr constrs = do
    constrs <- concat <$> mapM ((getDataCon =<<) . getConData) (constr : constrs)
    tags    <- catMaybes <$> mapM getConstrTag' constrs
    let tag =  head $ map Tag [0..] \\ tags
    putConstrTag constr tag
    return tag

getConData :: QName -> Compile TCM QName
getConData con = do
    lmap <- lift (gets (TM.sigDefinitions . TM.stImports))
    case HM.lookup con lmap of
        Just def -> case theDef def of
            c@(TM.Constructor{}) -> return $ TM.conData c
            _                 -> __IMPOSSIBLE__
        Nothing -> __IMPOSSIBLE__

getDataCon :: QName -> Compile TCM [QName]
getDataCon con = do
    lmap <- lift (gets (TM.sigDefinitions . TM.stImports))
    case HM.lookup con lmap of
        Just def -> case theDef def of
            d@(TM.Datatype{}) -> return $ TM.dataCons d
            r@(TM.Record{})   -> return [ TM.recCon r]
            _                 -> __IMPOSSIBLE__
        Nothing -> __IMPOSSIBLE__

getConstrTag :: QName -> Compile TCM Tag
getConstrTag con = lookInterface (M.lookup con . constrTags)
                                 (assignConstrTag con)

getConstrTag' :: QName -> Compile TCM (Maybe Tag)
getConstrTag' con = do
    cur <- gets curModule
    case M.lookup con (constrTags cur) of
        Just x -> return (Just x)
        Nothing -> do
            imps <- gets importedModules
            return $ M.lookup con (constrTags imps)

addDefName :: QName -> Compile TCM ()
addDefName q = do
    modifyEI $ \s -> s {definitions = S.insert (unqname q) $ definitions s }

topBindings :: Compile TCM (Set Var)
topBindings = S.union <$> gets (definitions . importedModules) <*> gets (definitions . curModule)

getConArity :: QName -> Compile TCM Int
getConArity n = lookInterface (M.lookup n . conArity) __IMPOSSIBLE__

putConArity :: QName -> Int -> Compile TCM ()
putConArity n p = modifyEI $ \s -> s { conArity = M.insert n p (conArity s) }

putMain :: QName -> Compile TCM ()
putMain m = modifyEI $ \s -> s { mainName = Just m }

getMain :: Compile TCM Var
getMain = maybe (epicError "Where is main? :(") (return . unqname) =<< getsEI mainName

lookInterface :: (EInterface -> Maybe a) -> Compile TCM a -> Compile TCM a
lookInterface f def = do
    cur <- gets curModule
    case f cur of
        Just x -> return x
        Nothing -> do
            imps <- gets importedModules
            case f imps of
                Nothing -> def
                Just x  -> return x

constrInScope :: QName -> Compile TCM Bool
constrInScope name = do
    cur <- gets curModule
    case M.lookup name (constrTags cur) of
        Just x -> return True
        Nothing -> do
            imps <- gets importedModules
            case M.lookup name (constrTags imps) of
                Nothing -> return False
                Just x  -> return True

getForcedArgs :: QName -> Compile TCM ForcedArgs
getForcedArgs q = lookInterface (M.lookup q . forcedArgs) __IMPOSSIBLE__

putForcedArgs :: QName -> ForcedArgs -> Compile TCM ()
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
bindExpr :: Expr -> (Var -> Compile TCM Expr) -> Compile TCM Expr
bindExpr expr f = case expr of
  AuxAST.Var v -> f v
  _     -> do
      v <- newName
      lett v expr <$> f v
