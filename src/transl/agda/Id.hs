-- | Identifiers with Position information. Symbol tables.
module Id(
       Id, mkId, dummyId, hypId, internalHypId, isDummyId,getIdString, getIdPosition, toId,
       getIdNo, UId, mkUId, internalUId, isInternalUId, dummyUId, isDummyUId,toDummyUId,getUIdString,
       getUIdPosition, toUId,sameId, eqAsId, getUIdNo,putUIdNo,
       getUIdFString, isModuleId, isModuleString, getFixity, SymTab,
       addId, lookupST, initST, domST, rangeST, freshId, freshId',
       isBinOp, remId, putUIdPosition , ppId, pprId, ppInfix , ppUId, pprUId,
       isRArrow, isBRArrow,symTabToList
       ) where
import PPrint
import FString
import Position
import PreStrings
import BinParse(Fixity(..))
import AgdaTrace
import Lex (isSym)
import Data.Maybe(catMaybes)
import Util(remDup)
import Data.List(sort)
import Data.Char(isAlpha)
import Data.Map ( Map )
import qualified Data.Map as Map

data Id = Id Position FString



instance Eq Id where
        Id _ fs == Id _ fs'  =  fs == fs'

instance Ord Id where
        Id _ fs <= Id _ fs'  =  getFString fs <= getFString fs'

mkId pos fs = Id pos fs

hypId p = Id p fsHypvar
internalHypId  = Id noPosition fsInternalHypvar


dummyId = Id noPosition fsUnderscore
isDummyId (Id _ fs) = fs == fsUnderscore

instance PPrint Id where
      pPrint _ _ (Id _ fs) = text (getFString fs)

instance Show Id where
      show (Id _ fs) = getFString fs

getIdString :: Id -> String
getIdString (Id _ fs) = getFString fs

getIdPosition :: Id -> Position
getIdPosition (Id p _) = p

getIdFString :: Id -> FString
getIdFString (Id _ fs) = fs

getIdNo :: Id -> Int
getIdNo (Id _ fs) = getFStrNo fs

data UId = UId Position FString !Int

instance Eq UId where
        UId _ _ i == UId _ _ i'  =  i == i'

instance Ord UId where
        UId _ fs _ <= UId _ fs' _ =  getFString fs <= getFString fs'

instance Show UId where
    showsPrec p (UId _ fs i) =  \s -> showsPrec p fs (showsPrec p i s)


mkUId :: Id -> Int -> UId
mkUId (Id pos fs) u = UId pos fs u

internalUId pos fs u = UId pos fs (-u)
isInternalUId (UId _ _ i) = i < 0

dummyUId :: Position -> FString -> UId
dummyUId p fs = UId p fs 0

toDummyUId :: Id -> UId
toDummyUId (Id p fs) = dummyUId p fs

isDummyUId (UId _ _ i) = i == 0

instance PPrint UId where
     pPrint d _ x@(UId _ fs u) =
        if d == PDDebug then
            text (getFString fs ++ "#" ++ show u)
        else if (isInternalUId x) then
                 text (getFString fs++"Internal")
             else text (getFString fs)

getUIdString :: UId -> String
getUIdString (UId _ fs _) = getFString fs

getUIdFString :: UId -> FString
getUIdFString (UId _ fs _) = fs

getUIdPosition :: UId -> Position
getUIdPosition (UId p _ _) = p

getUIdNo :: UId -> Int
getUIdNo (UId _ _ n) = n

putUIdNo :: UId -> Int -> UId
putUIdNo (UId p fs _) n = UId p fs n

putUIdPosition :: UId -> Position -> UId
putUIdPosition (UId _ fs u) pos = UId pos fs u

toId (UId p fs n)  = Id p fs                                  -- a hack

toUId (Id p fs) u = UId p fs u




{-
mkTmpUId :: Int -> UId
mkTmpUId u = UId noPosition (tmpFString u ("_"++show u)) u

isTmpUId :: UId -> Bool
isTmpUId (UId _ fs _) = isTmpFString fs
-}

sameId :: Id -> UId -> Bool
sameId (Id _ fs) (UId _ fs' _) = fs == fs'

eqAsId :: UId -> UId -> Bool
eqAsId (UId _ fs _) (UId _ fs' _) = fs == fs'

isModuleId i = isModuleString (getIdString i)
isModuleString s = '$' `elem` s

getFixity :: Id -> Fixity
getFixity i =
    case getIdString i of
    ","   -> FInfixr (-1)
    "->"  -> FInfixr 0
    "==>"  -> FInfixr 0
    "handle" -> FInfix 0
    "handle_" -> FInfix 0
    "|->" -> FInfixr 0
    "$"   -> FInfixr 0
    ">>"  -> FInfixl 1
    ">>=" -> FInfixl 1
    "\xd7"-> FInfixr 1	-- ×
    "||"  -> FInfixr 2
    "&&"  -> FInfixr 3
    "=="  -> FInfix  4
    "/="  -> FInfix  4
    "<="  -> FInfix  4
    ">="  -> FInfix  4
    "<"   -> FInfix  4
    ">"   -> FInfix  4
    ":"   -> FInfixr 5
    "++"  -> FInfixr 5
    "+"   -> FInfixl 6
    "-"   -> FInfixl 6
    "*"   -> FInfixl 7
    "/"   -> FInfixl 7
    "\xb7"   -> FInfixr 8   -- ·
    "\xb0"   -> FInfixr 8   -- °
    _     -> FInfixl 9


isBinOp :: Id -> Bool
isBinOp i = isSym $ head $ getIdString i

isRArrow :: Id -> Bool
isRArrow (Id p fs) = fs == fsRArrow

isBRArrow :: Id -> Bool
isBRArrow (Id p fs) = fs == fsBRArrow

appendId :: StrTable -> Id -> String -> (StrTable,Id)
appendId t n s = let (t',fs) = hmkFString t (getIdString n ++ s)
                 in (t',mkId noPosition fs)


freshId :: StrTable -> [Id] -> Id -> (StrTable,Id)
freshId t xs x
    | isDummyId x = (t,x)
    | x `notElem` xs = (t,x)
    | x' `notElem` xs =  (t',x')
    | otherwise = freshId' t x xs 0
    where  (t',x') = appendId t x "'"            -- "'"
           freshId' t x xs n = let (t',x') = appendId t x (show n)
                               in if x' `elem` xs
                                     then freshId' t x xs (n+1)
                                     else (t',x')


freshId' :: StrTable -> [Id] -> String -> (StrTable,Id)
freshId' t xs s = let (t',fs) = hmkFString t s
                  in freshId t' xs (mkId noPosition fs)


type SymTab = Map Id UId

instance (PPrint a, PPrint b) => PPrint (Map a b) where
  pPrint d p ls = pPrint d p (Map.toList ls)

-- instance PPrint SymTab where
--     pPrint d p (SymTab ls) = pPrint d p ls

addId :: Id -> UId -> SymTab -> SymTab
addId x x' st = Map.insert x x' st

remId :: Id -> SymTab -> SymTab
remId x st = Map.delete x st


lookupST:: SymTab -> Id -> Maybe UId
lookupST st n = Map.lookup n st

initST :: SymTab
initST =  Map.empty


domST :: SymTab -> [Id]
domST = Map.keys

rangeST :: SymTab -> [UId]
rangeST = Map.elems


symTabToList :: SymTab -> [(Id,UId)]
symTabToList = Map.toList




{-- from CSyntax --}

ppId :: PDetail -> Id -> IText
ppId d i =
    case getIdString i of
    s@(c:_) | isAlpha c || c == '_' -> text s
    s -> text ("("++s++")")

pprId :: Id -> String
pprId i = pIText (ppId PDReadable i)

ppInfix :: PDetail -> Id -> IText
ppInfix d i =
    (case getIdString i of
      s@(c:_) | isAlpha c -> text("`"++s++"`")
      s -> text s)



{- from ISyntax -}

ppUId :: PDetail -> UId -> IText
ppUId PDDebug i = ppId  PDDebug (toId i)~.text("#"++(show $ getUIdNo i))
ppUId d i
    | isInternalUId i = pPrint d 0 i
    | otherwise = ppId d (toId i)

pprUId :: UId -> String
pprUId c = pIText (ppUId PDReadable c)
