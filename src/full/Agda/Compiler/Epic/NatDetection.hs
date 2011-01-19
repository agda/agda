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

import Agda.TypeChecking.Monad
import Agda.Syntax.Internal
import Agda.Syntax.Common

import Agda.Compiler.Epic.CompileState hiding (conPars)

-- | Get a list of all the datatypes that look like nats. The [QName] is on the
--   form [zeroConstr, sucConstr]
getNatish :: MonadTCM m => Compile m [(IrrFilter,[QName])]
getNatish = do
  sig <- lift (gets (sigDefinitions . stImports))
  let defs = M.toList sig
  fmap catMaybes $ forM defs $ \(q, def) ->
    case theDef def of
      d@(Datatype {}) -> do -- A datatype ...
          case dataCons d of
              constrs | length constrs == 2 -> do -- with two constructors ...
                  z <- zip constrs <$> mapM getIrrFilter constrs
                  case sortBy (compare `on` nrRel . snd) z of
                    [(cz,fz), (cs,fs)] -> do
                      let ts = defType $ sig M.! cs
                          nr = fromIntegral $ dataPars d
                      return $ do
                       guard (nrRel fz == 0) -- where one constructor has zero arguments ...
                       guard (nrRel fs == 1) -- and the other one one argument ...
                       guard (isRec ((fromJust $ elemIndex True fs) + nr) ts q) -- which is recursive.
                       return (fs, [cz, cs]) -- It's natish!
                    _ -> return Nothing
              _       -> return Nothing
      _ -> return Nothing

-- | Count the number of relevant arguments
nrRel :: IrrFilter -> Integer
nrRel = sum . map (const 1) . filter id

-- | Check if argument n is recursive
isRec :: Int -> Type -> QName -> Bool
isRec 0 (El _ t) dat = case t of
    Fun arg _ -> argIsDef (unArg arg) dat
    Pi  arg _ -> argIsDef (unArg arg) dat
    _       -> False
isRec n (El _ t) dat = case t of
    Pi  _ ab  -> isRec (n - 1) (absBody ab) dat
    Fun _ typ -> isRec (n - 1) typ           dat
    _           -> False

argIsDef :: Type -> QName -> Bool
argIsDef (El _ t) dat = case t of
    Def q _ -> q == dat
    _       -> False
