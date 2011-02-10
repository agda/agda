{-# LANGUAGE CPP #-}

-- | Contains the state monad that the compiler works in and some functions
--   for tampering with the state.
module Agda.Compiler.Epic.CompileState where

import Control.Applicative
import Control.Monad.State
import Data.Map(Map)
import qualified Data.Map as M
import Data.Maybe
import Data.Set(Set)
import qualified Data.Set as S

import Agda.Compiler.Epic.AuxAST
import Agda.Syntax.Internal
import Agda.Syntax.Common
import Agda.TypeChecking.Monad (MonadTCM, internalError, defType, theDef, getConstInfo)
import qualified Agda.TypeChecking.Monad as M
import Agda.TypeChecking.Reduce

#include "../../undefined.h"
import Agda.Utils.Impossible

type IrrFilter = [Bool]

-- | Stuff we need in our compiler
data CompileState = CompileState
    { dataDecls     :: Map QName Tag
    , nameSupply    :: [Var]
    , definitions   :: Set Var
    , defDelayed    :: Map QName Bool
    , conPars       :: Map QName Int
    , mainName      :: Maybe QName
    , irrFilters    :: Map QName IrrFilter
    } deriving Show

-- | The initial (empty) state
initCompileState :: CompileState
initCompileState = CompileState
    { dataDecls     = M.empty
    , nameSupply    = map (('h':) . show) [0 :: Integer ..]
    , definitions   = S.fromList primTopBindings
    , defDelayed    = M.empty
    , conPars       = M.empty
    , mainName      = Nothing
    , irrFilters    = M.empty
    }
  where
    -- | For the lambda-lifter not to lift known primitive functions.
    primTopBindings :: [Var]
    primTopBindings = ["primNatCaseZD", "primNatCaseZS", "primBoolCase", "primUnit", "primSharp"]

-- | Compiler monad
type Compile = StateT CompileState

epicError :: MonadTCM m => String -> Compile m a
epicError = lift . internalError

-- | Create a name which can be used in Epic code from a QName.
unqname :: QName -> Var
unqname qn = case nameId $ qnameName qn of
    NameId name modul -> 'd' : show modul
                     ++ "_" ++ show name

-- * State modifiers

getDelayed :: MonadTCM m => QName -> Compile m Bool
getDelayed q = fromMaybe False <$> gets (M.lookup q . defDelayed)

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
    modify $ \s -> s {definitions = S.insert (unqname q) $ definitions s }
    when ("main" == show (qnameName q)) (putMain q) -- hax

topBindings :: Monad m => Compile m (Set Var)
topBindings = gets definitions

getConPar :: MonadTCM m => QName -> Compile m Int
getConPar n = fromMaybe __IMPOSSIBLE__ <$> M.lookup n <$> gets conPars

putConPar :: Monad m => QName -> Int -> Compile m ()
putConPar n p = modify $ \s -> s { conPars = M.insert n p (conPars s) }

putMain :: Monad m => QName -> Compile m ()
putMain m = modify $ \s -> s { mainName = Just m }

getMain :: MonadTCM m => Compile m Var
getMain = maybe (epicError "Where is main? :(") (return . unqname) =<< gets mainName

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
constructorArity :: (MonadTCM tcm, Num a) => QName -> tcm a
constructorArity q = do
  def <- getConstInfo q
  a <- normalise $ defType def
  case theDef def of
    M.Constructor{ M.conPars = np } -> return . fromIntegral $ arity a - np
    _ -> internalError $ "constructorArity: non constructor: " ++ show q

