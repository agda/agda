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
import Agda.TypeChecking.Monad (MonadTCM, internalError, defType, theDef, getConstInfo)
import qualified Agda.TypeChecking.Monad as M
import Agda.TypeChecking.Reduce

#include "../../undefined.h"
import Agda.Utils.Impossible
import Agda.Utils.Monad


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
    return $ maybe __IMPOSSIBLE__ defType (M.lookup q map)

-- | Create a name which can be used in Epic code from a QName.
unqname :: QName -> Var
unqname qn = case nameId $ qnameName qn of
    NameId name modul -> 'd' : show modul
                     ++ "_" ++ show name

-- * State modifiers

getDelayed :: MonadTCM m => QName -> Compile m Bool
getDelayed q = lookInterface (M.lookup q . defDelayed) (return False)

putDelayed :: Monad m => QName -> Bool -> Compile m ()
putDelayed q d = modify $ \s -> s {defDelayed = M.insert q d (defDelayed s)}

newName :: Monad m => Compile m Var
newName = do
    n:ns <- gets nameSupply
    modify $ \s -> s { nameSupply = ns}
    return n

-- | Add a data declaration by giving a list of its constructors.
--   Tags will be created and saved.
addDataDecl :: Monad m => [QName] -> Compile m ()
addDataDecl ts = modify
    $ \s -> s { dataDecls = M.union (M.fromList $ zip ts [0..]) (dataDecls s)}

getConstrTag :: Monad m => QName -> Compile m Tag
getConstrTag con = gets $ fromMaybe __IMPOSSIBLE__
                        . M.lookup con
                        . dataDecls

addDefName :: Monad m => QName -> Compile m ()
addDefName q = do
    modifyEI $ \s -> s {definitions = S.insert (unqname q) $ definitions s }

topBindings :: Monad m => Compile m (Set Var)
topBindings = gets definitions

getConPar :: MonadTCM m => QName -> Compile m Int
getConPar n = fromMaybe __IMPOSSIBLE__ <$> M.lookup n <$> gets conPars

putConPar :: Monad m => QName -> Int -> Compile m ()
putConPar n p = modify $ \s -> s { conPars = M.insert n p (conPars s) }

putMain :: Monad m => QName -> Compile m ()
putMain m = modify $ \s -> s { mainName = Just m }

getMain :: Compile TCM Var
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

getIrrFilter :: Monad m => QName -> Compile m IrrFilter
getIrrFilter q = gets $ fromMaybe __IMPOSSIBLE__
                      . M.lookup q
                      . irrFilters

putIrrFilter :: Monad m => QName -> IrrFilter -> Compile m ()
putIrrFilter n f = modify $ \s -> s {irrFilters = M.insert n f $ irrFilters s}

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
bindExpr :: MonadTCM m => Expr -> (Var -> Compile m Expr) -> Compile m Expr
bindExpr expr f = case expr of
  AuxAST.Var v -> f v
  _     -> do
      v <- newName
      lett v expr <$> f v
