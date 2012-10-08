{-# LANGUAGE CPP #-}
-- | Detect if a datatype could be represented as a primitive integer.
--   If it has one constructor with no arguments and one with a recursive
--   argument this is true. This is done using IrrFilters which filter out
--   forced arguments, so for example Fin becomes primitive.
module Agda.Compiler.Epic.NatDetection where

import Control.Applicative
import Control.Monad
import Control.Monad.State
import Data.Function
import Data.List
import qualified Data.Map as M
import Data.Maybe

import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Substitute
import Agda.Utils.Monad (andM)

import Agda.Compiler.Epic.CompileState
import Agda.Compiler.Epic.Interface

#include "../../undefined.h"
import Agda.Utils.Impossible
import qualified Agda.Utils.HashMap as HM

-- | Get a list of all the datatypes that look like nats. The [QName] is on the
--   form [zeroConstr, sucConstr]
getNatish :: Compile TCM [(ForcedArgs, [QName])]
getNatish = do
  sig <- lift (gets (sigDefinitions . stImports))
  let defs = HM.toList sig
  fmap catMaybes $ forM defs $ \(q, def) ->
    case theDef def of
      d@(Datatype {}) -> isNatish q d

      _ -> return Nothing

isNatish :: QName -> Defn -> Compile TCM (Maybe (ForcedArgs, [QName]))
isNatish q d = do -- A datatype ...
    case dataCons d of
        constrs | length constrs == 2 -> do -- with two constructors ...
            b <- andM $ map constrInScope constrs
            if b
              then do
                z <- zip constrs <$> mapM getForcedArgs constrs
                case sortBy (compare `on` nrRel . snd) z of
                  [(cz,fz), (cs,fs)] -> do
                    sig <- lift (gets (sigDefinitions . stImports))
                    let ts = defType $ sig HM.! cs
                        nr = dataPars d
                    return $ do
                     guard (nrRel fz == 0) -- where one constructor has zero arguments ...
                     guard (nrRel fs == 1) -- and the other one one argument ...
                     guard (isRec ((fromMaybe __IMPOSSIBLE__ $ elemIndex NotForced fs) + nr) ts q) -- which is recursive.
                     return (fs, [cz, cs]) -- It's natish!
                  _ -> return Nothing
              else return Nothing
        _       -> return Nothing

-- | Count the number of relevant arguments
nrRel :: ForcedArgs -> Integer
nrRel = sum . map (const 1) . filter (== NotForced)

-- | Check if argument n is recursive
isRec :: Int -> Type -> QName -> Bool
isRec 0 (El _ t) dat = case t of
    Pi  arg _ -> argIsDef (unDom arg) dat
    _         -> False
isRec n (El _ t) dat = case t of
    Pi  _ ab  -> isRec (n - 1) (unAbs ab) dat
    _         -> False

argIsDef :: Type -> QName -> Bool
argIsDef (El _ t) dat = case t of
    Def q _ -> q == dat
    _       -> False
