
module TypeChecking.Monad.Debug where

import Syntax.Internal
import TypeChecking.Monad

newtype StoreElm = StoreElm (MetaId, MetaVariable)
instance Show StoreElm where show (StoreElm x) = storeElm2str x
storeElm2str (x, mv) = "?"++(show x)++(case mv of
    InstV v -> ":="++(show v)
    InstT a -> ":="++(show a)
    InstS s -> ":="++(show s)
    UnderScoreV a cIds -> ":"++(show a)++"|"++(show cIds)
    UnderScoreT s cIds -> ":"++(show s)++"|"++(show cIds)
    UnderScoreS cIds -> "|"++(show cIds)
    HoleV a cIds -> ":"++(show a)++"|"++(show cIds)
    HoleT s cIds -> ":"++(show s)++"|"++(show cIds)
  )

instance Show TCState where 
    show st = 
        "{genSymSt="++(show $ stNextMeta st)++
        ", metaSt="++(show $ map StoreElm $ stMetaStore st)++
        ", cnstrSt="++(show $ stConstraints st)++
        ", sigSt="++(show $ stSignature st)++
        "}"


