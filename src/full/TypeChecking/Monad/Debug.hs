
module TypeChecking.Monad.Debug where

import qualified Data.Map as Map
import Control.Monad.Trans

import Syntax.Internal
import TypeChecking.Monad

newtype StoreElm = StoreElm (MetaId, MetaVariable)
instance Show StoreElm where show (StoreElm x) = storeElm2str x
storeElm2str (x, mv) = "?"++(show x)++(case mv of
    InstV _ v _ -> ":="++(show v)
    InstT _ a -> ":="++(show a)
    InstS _ s -> ":="++(show s)
    UnderScoreV _ a cIds -> ":"++(show a)++"|"++(show cIds)
    UnderScoreT _ s cIds -> "::"++(show s)++"|"++(show cIds)
    UnderScoreS _ cIds -> "|"++(show cIds)
    HoleV _ a cIds -> ":"++(show a)++"|"++(show cIds)
    HoleT _ s cIds -> "::"++(show s)++"|"++(show cIds)
  )

instance Show TCState where 
    show st = 
        "{genSymSt="++(show $ stFreshThings st)++
        ", metaSt="++(show $ map StoreElm $ Map.assocs $ stMetaStore st)++
        ", cnstrSt="++(show $ stConstraints st)++
        ", sigSt="++(show $ stSignature st)++
        "}"

debug :: String -> TCM ()
debug s = liftIO $ putStrLn s

