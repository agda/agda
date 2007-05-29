module Compiler.Alonzo.Names where
import Language.Haskell.Syntax
import Syntax.Abstract.Name
import Syntax.Common

conStr :: Name -> String
conStr n = "C" ++ (show $ numOfName n)

dfStr :: Name -> String
dfStr n = "d" ++ (show $ numOfName n)
-- dfStr (Name (NameId i) c) = "d" ++ (show i)

conQStr :: QName -> String
conQStr qn = "C" ++ (show $ numOfQName qn)

dfQStr :: QName -> String
dfQStr qn = "d" ++ (show $ numOfQName qn)

-- For now a hack that allows local modules, but not hierarhical modules
moduleStr :: ModuleName -> String
-- moduleStr m = show m
moduleStr (MName (n:ns)) = show n
moduleStr (MName []) = error "Empty module list!"
conName :: Name -> HsName
conName = HsIdent . conStr

dataName :: Name -> HsName
dataName n = HsIdent $ "T" ++ (show (numOfName n))

-- dataQName :: QName -> HsQName
-- dataQName n = HsIdent $ "T" ++ (show (numOfName n))

dfName :: Name -> HsName
dfName = HsIdent . dfStr

dfNameSub :: Name -> Int -> HsName
dfNameSub name i = HsIdent id where
	id = (dfStr name) ++ "_" ++  (show i)

dfQName :: QName -> HsQName
dfQName (QName m n) 
  | (moduleStr m) == "RTP" = Qual (Module $ moduleStr m)(HsIdent $ "_"++(show n))
  | otherwise = Qual (Module $ moduleStr m) (dfName n)

conQName :: QName -> HsQName
conQName (QName m n)
  |(moduleStr m)=="RTP" = Qual (Module $ moduleStr m)  (HsIdent $ show n)
  | otherwise = Qual (Module $ moduleStr m) (conName n)

numOfName :: Name -> Int
numOfName n = i where
	id = nameId n
        (NameId i mi) = id


numOfQName :: QName -> Int
-- numOfQName (QName m (Name (NameId i) nc) ) = i
numOfQName = numOfName . qnameName


rtpQName :: String -> HsQName
rtpQName s = Qual (Module "RTP")(HsIdent $ ('_':s))
rtpCon s = Qual (Module "RTP")(HsIdent s)