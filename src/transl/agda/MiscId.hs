module MiscId where
import Position(noPosition)
import Id
import ISyntax
import PreStrings

hypId =  mkId noPosition fsHypvar
varId =  mkId noPosition fsVar
varId1 = mkId noPosition fsVar1
varId2 =  mkId noPosition  fsVar2
varId3 =  mkId noPosition fsVar3
varIda =  mkId noPosition fsVara
varIdb =  mkId noPosition fsVarb
typeVarId =  mkId noPosition fsTypeVar
setoidId = mkId noPosition fsSetoid
elemId = mkId noPosition fsElem
equalId = mkId noPosition fsEqual
monadId = mkId noPosition fsMonad
bindId =  mkId noPosition fsBind
bindId_ =  mkId noPosition fsBind_
returnId = mkId noPosition fsReturn
failId = mkId noPosition fsFail
refId = mkId noPosition fsRef
symId = mkId noPosition fsSym
tranId = mkId noPosition  fsTran
elId = mkId noPosition fsEl
eqId = mkId noPosition fsEq
commaId = mkId noPosition fsComma
pairId = mkId noPosition fsPair
-- Change positions to a fixed prelude def.
charId = mkId noPosition fsChar
--charModId = mkId noPosition fsCharMod
stringId = mkId noPosition fsString
--stringModId = mkId noPosition fsStringMod
intId = mkId noPosition fsInt
--intModId = mkId noPosition fsIntMod
integerId = mkId noPosition fsInteger
--integerModId = mkId noPosition fsIntegerMod
boolId = mkId noPosition fsBool
--errorModId = mkId noPosition fsErrorMod
rationalId = mkId noPosition fsRational
--doubleModId = mkId noPosition fsDoubleMod

listId = mkId noPosition fsList
nilId = mkId noPosition fsNil
consId = mkId noPosition fsCons

--undefinedId = mkId noPosition fsUndefined
--undefinedTId = mkId noPosition fsUndefinedT
--undefinedTTId = mkId noPosition fsUndefinedTT

trueId = mkId noPosition fsTrue
falseId = mkId noPosition fsFalse

hypTypeId p = mkId p fsHypTypeVar
--hypTypeId' p = mkId p fsHypTypeVar'

hypTypeIdB p = mkId p fsHypTypeVarB

listVarHeadId = mkId noPosition fsListVarHead
listVarTailId = mkId noPosition fsListVarTail

monadName = mkId noPosition fsMonadName

--- JM
jmId = mkId noPosition fsJM
jmSameId = mkId noPosition fsSame
