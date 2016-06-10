{-# LANGUAGE CPP                 #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Agda.TypeChecking.Rules.Builtin
  ( bindBuiltin
  , bindBuiltinNoDef
  , bindPostulatedName
  , isUntypedBuiltin
  , bindUntypedBuiltin
  ) where

import Control.Applicative hiding (empty)
import Control.Monad
import Data.List (find)

import qualified Agda.Syntax.Abstract as A
import qualified Agda.Syntax.Abstract.Views as A
import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.Syntax.Position

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Monad.Builtin
import Agda.TypeChecking.Monad.SizedTypes ( builtinSizeHook )

import qualified Agda.TypeChecking.CompiledClause as CC
import Agda.TypeChecking.Conversion
import Agda.TypeChecking.Constraints
import Agda.TypeChecking.EtaContract
import Agda.TypeChecking.Irrelevance
import Agda.TypeChecking.Primitive
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Rules.Term ( checkExpr , inferExpr )

import {-# SOURCE #-} Agda.TypeChecking.Rules.Builtin.Coinduction
import {-# SOURCE #-} Agda.TypeChecking.Rewriting

import Agda.Utils.Except ( MonadError(catchError) )
import Agda.Utils.Maybe
import Agda.Utils.Monad
import Agda.Utils.Null
import Agda.Utils.Size

#include "undefined.h"
import Agda.Utils.Impossible

---------------------------------------------------------------------------
-- * Checking builtin pragmas
---------------------------------------------------------------------------

builtinPostulate :: TCM Type -> BuiltinDescriptor
builtinPostulate = BuiltinPostulate Relevant

coreBuiltins :: [BuiltinInfo]
coreBuiltins = map (\ (x, z) -> BuiltinInfo x z)
  [ (builtinList               |-> BuiltinData (tset --> tset) [builtinNil, builtinCons])
  , (builtinArg                |-> BuiltinData (tset --> tset) [builtinArgArg])
  , (builtinAbs                |-> BuiltinData (tset --> tset) [builtinAbsAbs])
  , (builtinArgInfo            |-> BuiltinData tset [builtinArgArgInfo])
  , (builtinBool               |-> BuiltinData tset [builtinTrue, builtinFalse])
  , (builtinNat                |-> BuiltinData tset [builtinZero, builtinSuc])
  , (builtinUnit               |-> BuiltinData tset [builtinUnitUnit])  -- actually record, but they are treated the same
  , (builtinAgdaLiteral        |-> BuiltinData tset [builtinAgdaLitNat, builtinAgdaLitFloat,
                                                     builtinAgdaLitChar, builtinAgdaLitString,
                                                     builtinAgdaLitQName, builtinAgdaLitMeta])
  , (builtinAgdaPattern        |-> BuiltinData tset [builtinAgdaPatVar, builtinAgdaPatCon, builtinAgdaPatDot,
                                                     builtinAgdaPatLit, builtinAgdaPatProj, builtinAgdaPatAbsurd])
  , (builtinAgdaPatVar         |-> BuiltinDataCons (tstring --> tpat))
  , (builtinAgdaPatCon         |-> BuiltinDataCons (tqname --> tlist (targ tpat) --> tpat))
  , (builtinAgdaPatDot         |-> BuiltinDataCons tpat)
  , (builtinAgdaPatLit         |-> BuiltinDataCons (tliteral --> tpat))
  , (builtinAgdaPatProj        |-> BuiltinDataCons (tqname --> tpat))
  , (builtinAgdaPatAbsurd      |-> BuiltinDataCons tpat)
  , (builtinLevel              |-> builtinPostulate tset)
  , (builtinInteger            |-> BuiltinData tset [builtinIntegerPos, builtinIntegerNegSuc])
  , (builtinIntegerPos         |-> BuiltinDataCons (tnat --> tinteger))
  , (builtinIntegerNegSuc      |-> BuiltinDataCons (tnat --> tinteger))
  , (builtinFloat              |-> builtinPostulate tset)
  , (builtinChar               |-> builtinPostulate tset)
  , (builtinString             |-> builtinPostulate tset)
  , (builtinQName              |-> builtinPostulate tset)
  , (builtinAgdaMeta           |-> builtinPostulate tset)
  , (builtinIO                 |-> builtinPostulate (tset --> tset))
  , (builtinAgdaSort           |-> BuiltinData tset [builtinAgdaSortSet, builtinAgdaSortLit, builtinAgdaSortUnsupported])
  , (builtinAgdaTerm           |-> BuiltinData tset
                                     [ builtinAgdaTermVar, builtinAgdaTermLam, builtinAgdaTermExtLam
                                     , builtinAgdaTermDef, builtinAgdaTermCon
                                     , builtinAgdaTermPi, builtinAgdaTermSort
                                     , builtinAgdaTermLit, builtinAgdaTermMeta
                                     , builtinAgdaTermUnsupported])
  , builtinAgdaErrorPart       |-> BuiltinData tset [ builtinAgdaErrorPartString, builtinAgdaErrorPartTerm, builtinAgdaErrorPartName ]
  , builtinAgdaErrorPartString |-> BuiltinDataCons (tstring --> terrorpart)
  , builtinAgdaErrorPartTerm   |-> BuiltinDataCons (tterm --> terrorpart)
  , builtinAgdaErrorPartName   |-> BuiltinDataCons (tqname --> terrorpart)
  , (builtinEquality           |-> BuiltinData (hPi "a" (el primLevel) $
                                                hPi "A" (return $ sort $ varSort 0) $
                                                (El (varSort 1) <$> varM 0) -->
                                                (El (varSort 1) <$> varM 0) -->
                                                return (sort $ varSort 1))
                                               [builtinRefl])
  , (builtinHiding             |-> BuiltinData tset [builtinHidden, builtinInstance, builtinVisible])
  , (builtinRelevance          |-> BuiltinData tset [builtinRelevant, builtinIrrelevant])
  , (builtinRefl               |-> BuiltinDataCons (hPi "a" (el primLevel) $
                                                    hPi "A" (return $ sort $ varSort 0) $
                                                    hPi "x" (El (varSort 1) <$> varM 0) $
                                                    El (varSort 2) <$> primEquality <#> varM 2 <#> varM 1 <@> varM 0 <@> varM 0))
  , (builtinRewrite           |-> BuiltinUnknown Nothing verifyBuiltinRewrite)
  , (builtinNil                |-> BuiltinDataCons (hPi "A" tset (el (list v0))))
  , (builtinCons               |-> BuiltinDataCons (hPi "A" tset (tv0 --> el (list v0) --> el (list v0))))
  , (builtinZero               |-> BuiltinDataCons tnat)
  , (builtinSuc                |-> BuiltinDataCons (tnat --> tnat))
  , (builtinTrue               |-> BuiltinDataCons tbool)
  , (builtinFalse              |-> BuiltinDataCons tbool)
  , (builtinArgArg             |-> BuiltinDataCons (hPi "A" tset (targinfo --> tv0 --> targ tv0)))
  , (builtinAbsAbs             |-> BuiltinDataCons (hPi "A" tset (tstring  --> tv0 --> tabs tv0)))
  , (builtinArgArgInfo         |-> BuiltinDataCons (thiding --> trelevance --> targinfo))
  , (builtinAgdaTermVar        |-> BuiltinDataCons (tnat --> targs --> tterm))
  , (builtinAgdaTermLam        |-> BuiltinDataCons (thiding --> tabs tterm --> tterm))
  , (builtinAgdaTermExtLam     |-> BuiltinDataCons (tlist tclause --> targs --> tterm))
  , (builtinAgdaTermDef        |-> BuiltinDataCons (tqname --> targs --> tterm))
  , (builtinAgdaTermCon        |-> BuiltinDataCons (tqname --> targs --> tterm))
  , (builtinAgdaTermPi         |-> BuiltinDataCons (targ ttype --> tabs ttype --> tterm))
  , (builtinAgdaTermSort       |-> BuiltinDataCons (tsort --> tterm))
  , (builtinAgdaTermLit        |-> BuiltinDataCons (tliteral --> tterm))
  , (builtinAgdaTermMeta         |-> BuiltinDataCons (tmeta --> targs --> tterm))
  , (builtinAgdaTermUnsupported|-> BuiltinDataCons tterm)
  , (builtinAgdaLitNat    |-> BuiltinDataCons (tnat --> tliteral))
  , (builtinAgdaLitFloat  |-> BuiltinDataCons (tfloat --> tliteral))
  , (builtinAgdaLitChar   |-> BuiltinDataCons (tchar --> tliteral))
  , (builtinAgdaLitString |-> BuiltinDataCons (tstring --> tliteral))
  , (builtinAgdaLitQName  |-> BuiltinDataCons (tqname --> tliteral))
  , (builtinAgdaLitMeta   |-> BuiltinDataCons (tmeta --> tliteral))
  , (builtinHidden             |-> BuiltinDataCons thiding)
  , (builtinInstance           |-> BuiltinDataCons thiding)
  , (builtinVisible            |-> BuiltinDataCons thiding)
  , (builtinRelevant           |-> BuiltinDataCons trelevance)
  , (builtinIrrelevant         |-> BuiltinDataCons trelevance)
  , (builtinSizeUniv           |-> builtinPostulate tSizeUniv) -- SizeUniv : SizeUniv
-- See comment on tSizeUniv: the following does not work currently.
--  , (builtinSizeUniv           |-> builtinPostulate tSetOmega) -- SizeUniv : Setω
  , (builtinSize               |-> builtinPostulate tSizeUniv)
  , (builtinSizeLt             |-> builtinPostulate (tsize ..--> tSizeUniv))
  , (builtinSizeSuc            |-> builtinPostulate (tsize --> tsize))
  , (builtinSizeInf            |-> builtinPostulate tsize)
  -- postulate max : {i : Size} -> Size< i -> Size< i -> Size< i
  , (builtinSizeMax            |-> builtinPostulate (tsize --> tsize --> tsize))
     -- (hPi "i" tsize $ let a = el $ primSizeLt <@> v0 in (a --> a --> a)))
  , (builtinAgdaSortSet        |-> BuiltinDataCons (tterm --> tsort))
  , (builtinAgdaSortLit        |-> BuiltinDataCons (tnat --> tsort))
  , (builtinAgdaSortUnsupported|-> BuiltinDataCons tsort)
  , (builtinNatPlus            |-> BuiltinPrim "primNatPlus" verifyPlus)
  , (builtinNatMinus           |-> BuiltinPrim "primNatMinus" verifyMinus)
  , (builtinNatTimes           |-> BuiltinPrim "primNatTimes" verifyTimes)
  , (builtinNatDivSucAux       |-> BuiltinPrim "primNatDivSucAux" verifyDivSucAux)
  , (builtinNatModSucAux       |-> BuiltinPrim "primNatModSucAux" verifyModSucAux)
  , (builtinNatEquals          |-> BuiltinPrim "primNatEquality" verifyEquals)
  , (builtinNatLess            |-> BuiltinPrim "primNatLess" verifyLess)
  , (builtinLevelZero          |-> BuiltinPrim "primLevelZero" (const $ return ()))
  , (builtinLevelSuc           |-> BuiltinPrim "primLevelSuc" (const $ return ()))
  , (builtinLevelMax           |-> BuiltinPrim "primLevelMax" verifyMax)
  , (builtinAgdaClause         |-> BuiltinData tset [builtinAgdaClauseClause, builtinAgdaClauseAbsurd])
  , (builtinAgdaClauseClause   |-> BuiltinDataCons (tlist (targ tpat) --> tterm --> tclause))
  , (builtinAgdaClauseAbsurd   |-> BuiltinDataCons (tlist (targ tpat) --> tclause))
  , (builtinAgdaDefinition            |-> BuiltinData tset [builtinAgdaDefinitionFunDef
                                                           ,builtinAgdaDefinitionDataDef
                                                           ,builtinAgdaDefinitionDataConstructor
                                                           ,builtinAgdaDefinitionRecordDef
                                                           ,builtinAgdaDefinitionPostulate
                                                           ,builtinAgdaDefinitionPrimitive])
  , (builtinAgdaDefinitionFunDef          |-> BuiltinDataCons (tlist tclause --> tdefn))
  , (builtinAgdaDefinitionDataDef         |-> BuiltinDataCons (tnat --> tlist tqname --> tdefn))
  , (builtinAgdaDefinitionDataConstructor |-> BuiltinDataCons (tqname --> tdefn))
  , (builtinAgdaDefinitionRecordDef       |-> BuiltinDataCons (tqname --> tdefn))
  , (builtinAgdaDefinitionPostulate       |-> BuiltinDataCons tdefn)
  , (builtinAgdaDefinitionPrimitive       |-> BuiltinDataCons tdefn)
  , builtinAgdaTCM       |-> builtinPostulate (hPi "a" tlevel $ tsetL 0 --> tsetL 0)
  , builtinAgdaTCMReturn |-> builtinPostulate (hPi "a" tlevel  $
                                               hPi "A" (tsetL 0) $
                                               elV 1 (varM 0) --> tTCM 1 (varM 0))
  , builtinAgdaTCMBind   |-> builtinPostulate (hPi "a" tlevel  $ hPi "b" tlevel $
                                               hPi "A" (tsetL 1) $ hPi "B" (tsetL 1) $
                                               tTCM 3 (varM 1) --> (elV 3 (varM 1) --> tTCM 2 (varM 0)) --> tTCM 2 (varM 0))
  , builtinAgdaTCMUnify      |-> builtinPostulate (tterm --> tterm --> tTCM_ primUnit)
  , builtinAgdaTCMTypeError  |-> builtinPostulate (hPi "a" tlevel $ hPi "A" (tsetL 0) $ tlist terrorpart --> tTCM 1 (varM 0))
  , builtinAgdaTCMInferType  |-> builtinPostulate (tterm --> tTCM_ primAgdaTerm)
  , builtinAgdaTCMCheckType  |-> builtinPostulate (tterm --> ttype --> tTCM_ primAgdaTerm)
  , builtinAgdaTCMNormalise  |-> builtinPostulate (tterm --> tTCM_ primAgdaTerm)
  , builtinAgdaTCMCatchError |-> builtinPostulate (hPi "a" tlevel $ hPi "A" (tsetL 0) $ tTCM 1 (varM 0) --> tTCM 1 (varM 0) --> tTCM 1 (varM 0))
  , builtinAgdaTCMGetContext |-> builtinPostulate (tTCM_ (unEl <$> tlist (targ ttype)))
  , builtinAgdaTCMExtendContext |-> builtinPostulate (hPi "a" tlevel $ hPi "A" (tsetL 0) $ targ ttype --> tTCM 1 (varM 0) --> tTCM 1 (varM 0))
  , builtinAgdaTCMInContext     |-> builtinPostulate (hPi "a" tlevel $ hPi "A" (tsetL 0) $ tlist (targ ttype) --> tTCM 1 (varM 0) --> tTCM 1 (varM 0))
  , builtinAgdaTCMFreshName     |-> builtinPostulate (tstring --> tTCM_ primQName)
  , builtinAgdaTCMDeclareDef    |-> builtinPostulate (targ tqname --> ttype --> tTCM_ primUnit)
  , builtinAgdaTCMDefineFun     |-> builtinPostulate (tqname --> tlist tclause --> tTCM_ primUnit)
  , builtinAgdaTCMGetType            |-> builtinPostulate (tqname --> tTCM_ primAgdaTerm)
  , builtinAgdaTCMGetDefinition      |-> builtinPostulate (tqname --> tTCM_ primAgdaDefinition)
  , builtinAgdaTCMQuoteTerm          |-> builtinPostulate (hPi "a" tlevel $ hPi "A" (tsetL 0) $ elV 1 (varM 0) --> tTCM_ primAgdaTerm)
  , builtinAgdaTCMUnquoteTerm        |-> builtinPostulate (hPi "a" tlevel $ hPi "A" (tsetL 0) $ tterm --> tTCM 1 (varM 0))
  , builtinAgdaTCMBlockOnMeta        |-> builtinPostulate (hPi "a" tlevel $ hPi "A" (tsetL 0) $ tmeta --> tTCM 1 (varM 0))
  , builtinAgdaTCMCommit             |-> builtinPostulate (tTCM_ primUnit)
  ]
  where
        (|->) = (,)

        v0 = varM 0
        v1 = varM 1
        v2 = varM 2
        v3 = varM 3

        tv0,tv1 :: TCM Type
        tv0 = el v0
        tv1 = el v1
        tv2 = el v2
        tv3 = el v3

        arg :: TCM Term -> TCM Term
        arg t = primArg <@> t

        elV x a = El (varSort x) <$> a

        tsetL l    = return $ sort (varSort l)
        tlevel     = el primLevel
        tlist x    = el $ list (fmap unEl x)
        targ x     = el (arg (fmap unEl x))
        tabs x     = el (primAbs <@> fmap unEl x)
        targs      = el (list (arg primAgdaTerm))
        tterm      = el primAgdaTerm
        terrorpart = el primAgdaErrorPart
        tnat       = el primNat
        tunit      = el primUnit
        tinteger   = el primInteger
        tfloat     = el primFloat
        tchar      = el primChar
        tstring    = el primString
        tqname     = el primQName
        tmeta      = el primAgdaMeta
        tsize      = El sSizeUniv <$> primSize
        tbool      = el primBool
        thiding    = el primHiding
        trelevance = el primRelevance
--        tcolors    = el (list primAgdaTerm) -- TODO guilhem
        targinfo   = el primArgInfo
        ttype      = el primAgdaTerm
        tsort      = el primAgdaSort
        tdefn      = el primAgdaDefinition
        tliteral   = el primAgdaLiteral
        tpat       = el primAgdaPattern
        tclause    = el primAgdaClause
        tTCM l a   = elV l (primAgdaTCM <#> varM l <@> a)
        tTCM_ a    = el (primAgdaTCM <#> primLevelZero <@> a)

        verifyPlus plus =
            verify ["n","m"] $ \(@@) zero suc (==) (===) choice -> do
                let m = var 0
                    n = var 1
                    x + y = plus @@ x @@ y

                -- We allow recursion on any argument
                choice
                    [ do n + zero  == n
                         n + suc m == suc (n + m)
                    , do suc n + m == suc (n + m)
                         zero  + m == m
                    ]

        verifyMinus minus =
            verify ["n","m"] $ \(@@) zero suc (==) (===) choice -> do
                let m = var 0
                    n = var 1
                    x - y = minus @@ x @@ y

                -- We allow recursion on any argument
                zero  - zero  == zero
                zero  - suc m == zero
                suc n - zero  == suc n
                suc n - suc m == (n - m)

        verifyTimes times = do
            plus <- primNatPlus
            verify ["n","m"] $ \(@@) zero suc (==) (===) choice -> do
                let m = var 0
                    n = var 1
                    x + y = plus  @@ x @@ y
                    x * y = times @@ x @@ y

                choice
                    [ do n * zero == zero
                         choice [ (n * suc m) == (n + (n * m))
                                , (n * suc m) == ((n * m) + n)
                                ]
                    , do zero * n == zero
                         choice [ (suc n * m) == (m + (n * m))
                                , (suc n * m) == ((n * m) + m)
                                ]
                    ]

        verifyDivSucAux dsAux =
            verify ["k","m","n","j"] $ \(@@) zero suc (==) (===) choice -> do
                let aux k m n j = dsAux @@ k @@ m @@ n @@ j
                    k           = var 0
                    m           = var 1
                    n           = var 2
                    j           = var 3

                aux k m zero    j       == k
                aux k m (suc n) zero    == aux (suc k) m n m
                aux k m (suc n) (suc j) == aux k m n j

        verifyModSucAux dsAux =
            verify ["k","m","n","j"] $ \(@@) zero suc (==) (===) choice -> do
                let aux k m n j = dsAux @@ k @@ m @@ n @@ j
                    k           = var 0
                    m           = var 1
                    n           = var 2
                    j           = var 3

                aux k m zero    j       == k
                aux k m (suc n) zero    == aux zero m n m
                aux k m (suc n) (suc j) == aux (suc k) m n j

        verifyEquals eq =
            verify ["n","m"] $ \(@@) zero suc (==) (===) choice -> do
            true  <- primTrue
            false <- primFalse
            let x == y = eq @@ x @@ y
                m      = var 0
                n      = var 1
            (zero  == zero ) === true
            (suc n == suc m) === (n == m)
            (suc n == zero ) === false
            (zero  == suc n) === false

        verifyLess leq =
            verify ["n","m"] $ \(@@) zero suc (==) (===) choice -> do
            true  <- primTrue
            false <- primFalse
            let x < y = leq @@ x @@ y
                m     = var 0
                n     = var 1
            (n     < zero)  === false
            (suc n < suc m) === (n < m)
            (zero  < suc m) === true

        verifyMax maxV = return ()  -- TODO: make max a postulate

        verify xs = verify' primNat primZero primSuc xs

        verify' ::  TCM Term -> TCM Term -> TCM Term ->
                    [String] -> ( (Term -> Term -> Term) -> Term -> (Term -> Term) ->
                                (Term -> Term -> TCM ()) ->
                                (Term -> Term -> TCM ()) ->
                                ([TCM ()] -> TCM ()) -> TCM a) -> TCM a
        verify' pNat pZero pSuc xs f = do
            nat  <- El (mkType 0) <$> pNat
            zero <- pZero
            s    <- pSuc
            let x == y  = noConstraints $ equalTerm nat x y
                -- Andreas: 2013-10-21 I put primBool here on the inside
                -- since some Nat-builtins do not require Bool-builtins
                x === y = do bool <- El (mkType 0) <$> primBool
                             noConstraints $ equalTerm bool x y
                suc n  = s `apply1` n
                choice = foldr1 (\x y -> x `catchError` \_ -> y)
            xs <- mapM freshName_ xs
            addContext (xs, domFromArg $ defaultArg nat) $ f apply1 zero suc (==) (===) choice


inductiveCheck :: String -> Int -> Term -> TCM ()
inductiveCheck b n t = do
    t <- etaContract =<< normalise t
    let err = typeError (NotInductive t)
    case ignoreSharing t of
      Def t _ -> do
        t <- theDef <$> getConstInfo t
        case t of
          Datatype { dataInduction = Inductive
                   , dataCons      = cs
                   }
            | length cs == n -> return ()
            | otherwise ->
              typeError $ GenericError $ unwords
                          [ "The builtin", b
                          , "must be a datatype with", show n
                          , "constructors" ]
          Record { recInduction = ind } | n == 1 && ind /= Just CoInductive -> return ()
          _ -> err
      _ -> err

-- | @bindPostulatedName builtin e m@ checks that @e@ is a postulated
-- name @q@, and binds the builtin @builtin@ to the term @m q def@,
-- where @def@ is the current 'Definition' of @q@.

bindPostulatedName ::
  String -> A.Expr -> (QName -> Definition -> TCM Term) -> TCM ()
bindPostulatedName builtin e m = do
  q   <- getName e
  def <- ignoreAbstractMode $ getConstInfo q
  case theDef def of
    Axiom {} -> bindBuiltinName builtin =<< m q def
    _        -> err
  where
  err = typeError $ GenericError $
          "The argument to BUILTIN " ++ builtin ++
          " must be a postulated name"

  getName (A.Def q)          = return q
  getName (A.ScopedExpr _ e) = getName e
  getName _                  = err

getDef :: Term -> TCM QName
getDef t = do
  t <- etaContract =<< normalise t
  case ignoreSharing t of
    Def d _ -> return d
    _ -> __IMPOSSIBLE__

bindAndSetHaskellType :: String -> String -> Term -> TCM ()
bindAndSetHaskellType b hs t = do
  d <- getDef t
  addHaskellType d hs
  bindBuiltinName b t

bindBuiltinBool :: Term -> TCM ()
bindBuiltinBool = bindAndSetHaskellType builtinBool "Bool"

bindBuiltinInt :: Term -> TCM ()
bindBuiltinInt = bindAndSetHaskellType builtinInteger "Integer"

bindBuiltinNat :: Term -> TCM ()
bindBuiltinNat t = do
  nat <- getDef t
  def <- theDef <$> getConstInfo nat
  case def of
    Datatype { dataCons = [c1, c2] } -> do
      bindBuiltinName builtinNat t
      let getArity c = arity <$> (normalise . defType =<< getConstInfo c)
      [a1, a2] <- mapM getArity [c1, c2]
      let (zero, suc) | a2 > a1   = (c1, c2)
                      | otherwise = (c2, c1)
          tnat = el primNat
          rerange = setRange (getRange nat)
      addHaskellType nat "Integer"
      bindBuiltinInfo (BuiltinInfo builtinZero $ BuiltinDataCons tnat)
                      (A.Con $ AmbQ [rerange zero])
      bindBuiltinInfo (BuiltinInfo builtinSuc  $ BuiltinDataCons (tnat --> tnat))
                      (A.Con $ AmbQ [rerange suc])
    _ -> __IMPOSSIBLE__

bindBuiltinUnit :: Term -> TCM ()
bindBuiltinUnit t = do
  unit <- getDef t
  def <- theDef <$> getConstInfo unit
  case def of
    Record { recFields = [], recConHead = con } -> do
      bindBuiltinName builtinUnit t
      bindBuiltinName builtinUnitUnit (Con con [])
    _ -> genericError "Builtin UNIT must be a singleton record type"

bindBuiltinInfo :: BuiltinInfo -> A.Expr -> TCM ()
bindBuiltinInfo i (A.ScopedExpr scope e) = setScope scope >> bindBuiltinInfo i e
bindBuiltinInfo (BuiltinInfo s d) e = do
    case d of
      BuiltinData t cs -> do
        e' <- checkExpr e =<< t
        let n = length cs
        inductiveCheck s n e'
        case () of
          _ | s == builtinBool    -> bindBuiltinBool e'
            | s == builtinNat     -> bindBuiltinNat e'
            | s == builtinInteger -> bindBuiltinInt e'
            | s == builtinUnit    -> bindBuiltinUnit e'
            | otherwise           -> bindBuiltinName s e'

      BuiltinDataCons t -> do

        let name (Lam h b)  = name (absBody b)
            name (Con c _)  = Con c []
            name (Shared p) = name $ ignoreSharing (derefPtr p)
            name _          = __IMPOSSIBLE__

        e' <- checkExpr e =<< t

        case e of
          A.Con _ -> return ()
          _       -> typeError $ BuiltinMustBeConstructor s e

        let v@(Con h []) = name e'
            c = conName h
        when (s == builtinTrue)  $ addHaskellCode c "Bool" "True"
        when (s == builtinFalse) $ addHaskellCode c "Bool" "False"
        bindBuiltinName s v

      BuiltinPrim pfname axioms -> do
        case e of
          A.Def qx -> do

            PrimImpl t pf <- lookupPrimitiveFunction pfname
            v <- checkExpr e t

            axioms v

            info <- getConstInfo qx
            let cls = defClauses info
                a   = defAbstract info
                mcc = defCompiled info
            bindPrimitive pfname $ pf { primFunName = qx }
            addConstant qx $ info { theDef = Primitive a pfname cls mcc }

            -- needed? yes, for checking equations for mul
            bindBuiltinName s v

          _ -> typeError $ GenericError $ "Builtin " ++ s ++ " must be bound to a function"

      BuiltinPostulate rel t -> do
        t' <- t
        e' <- applyRelevanceToContext rel $ checkExpr e t'
        let err = typeError $ GenericError $
                    "The argument to BUILTIN " ++ s ++ " must be a postulated name"
        case e of
          A.Def q -> do
            def <- ignoreAbstractMode $ getConstInfo q
            case theDef def of
              Axiom {} -> do
                builtinSizeHook s q t'
                when (s == builtinChar)   $ addHaskellType q "Char"
                when (s == builtinString) $ addHaskellType q "Data.Text.Text"
                when (s == builtinFloat)  $ addHaskellType q "Double"
                bindBuiltinName s e'
              _        -> err
          _ -> err

      BuiltinUnknown mt f -> do
        (v, t) <- caseMaybe mt (inferExpr e) $ \ tcmt -> do
          t <- tcmt
          (,t) <$> checkExpr e t
        f v t
        bindBuiltinName s v

-- | Bind a builtin thing to an expression.
bindBuiltin :: String -> A.Expr -> TCM ()
bindBuiltin b e = do
  unlessM ((0 ==) <$> getContextSize) $ typeError $ BuiltinInParameterisedModule b
  case b of
    _ | b == builtinZero  -> nowNat b
    _ | b == builtinSuc   -> nowNat b
    _ | b == builtinInf   -> bindBuiltinInf e
    _ | b == builtinSharp -> bindBuiltinSharp e
    _ | b == builtinFlat  -> bindBuiltinFlat e
    _ | Just i <- find ((b ==) . builtinName) coreBuiltins -> bindBuiltinInfo i e
    _ -> typeError $ NoSuchBuiltinName b
  where
    nowNat b = genericError $
      "Builtin " ++ b ++ " does no longer exist. " ++
      "It is now bound by BUILTIN " ++ builtinNat

isUntypedBuiltin :: String -> Bool
isUntypedBuiltin b = elem b [builtinFromNat, builtinFromNeg, builtinFromString]

bindUntypedBuiltin :: String -> A.Expr -> TCM ()
bindUntypedBuiltin b e =
  case A.unScope e of
    A.Def q  -> bindBuiltinName b (Def q [])
    A.Proj (AmbQ [q]) -> bindBuiltinName b (Def q [])
    e        -> genericError $ "The argument to BUILTIN " ++ b ++ " must be a defined unambiguous name"

-- | Bind a builtin thing to a new name.
bindBuiltinNoDef :: String -> A.QName -> TCM ()
bindBuiltinNoDef b q = do
  unlessM ((0 ==) <$> getContextSize) $ typeError $ BuiltinInParameterisedModule b
  case lookup b $ map (\ (BuiltinInfo b i) -> (b, i)) coreBuiltins of
    Just (BuiltinPostulate rel mt) -> do
      t <- mt
      addConstant q $ defaultDefn (setRelevance rel defaultArgInfo) q t def
      builtinSizeHook b q t
      bindBuiltinName b $ Def q []
      where
        -- Andreas, 2015-02-14
        -- Special treatment of SizeUniv, should maybe be a primitive.
        def | b == builtinSizeUniv = emptyFunction
                { funClauses = [ (empty :: Clause) { clauseBody = Body $ Sort sSizeUniv } ]
                , funCompiled = Just (CC.Done [] $ Sort sSizeUniv)
                , funTerminates = Just True
                }
            | otherwise = Axiom

    Just{}  -> __IMPOSSIBLE__
    Nothing -> __IMPOSSIBLE__ -- typeError $ NoSuchBuiltinName b
