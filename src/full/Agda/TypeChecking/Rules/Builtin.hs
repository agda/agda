{-# LANGUAGE PatternGuards, CPP #-}
module Agda.TypeChecking.Rules.Builtin (bindBuiltin, bindPostulatedName) where

import Control.Applicative
import Control.Monad
import Control.Monad.Error
import Data.Maybe
import Data.List (find)

import qualified Agda.Syntax.Abstract as A
import Agda.Syntax.Internal
import Agda.Syntax.Common

import Agda.TypeChecking.EtaContract
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Monad.Builtin
import Agda.TypeChecking.Conversion
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Primitive
import Agda.TypeChecking.Constraints
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Irrelevance
import Agda.TypeChecking.SizedTypes ( builtinSizeHook )
import Agda.TypeChecking.Rules.Term ( checkExpr , inferExpr )
import {-# SOURCE #-} Agda.TypeChecking.Rules.Builtin.Coinduction

import Agda.Utils.Size
import Agda.Utils.Impossible

#include "../..//undefined.h"

---------------------------------------------------------------------------
-- * Checking builtin pragmas
---------------------------------------------------------------------------

builtinPostulate :: TCM Type -> BuiltinDescriptor
builtinPostulate = BuiltinPostulate Relevant

coreBuiltins :: [BuiltinInfo]
coreBuiltins = map (\(x,z) -> BuiltinInfo x z)
  [ (builtinList               |-> BuiltinData (tset --> tset) [builtinNil, builtinCons])
  , (builtinArg                |-> BuiltinData (tset --> tset) [builtinArgArg])
  , (builtinArgInfo            |-> BuiltinData tset [builtinArgArgInfo])
  , (builtinBool               |-> BuiltinData tset [builtinTrue, builtinFalse])
  , (builtinNat                |-> BuiltinData tset [builtinZero, builtinSuc])
  , (builtinLevel              |-> builtinPostulate tset)
  , (builtinInteger            |-> builtinPostulate tset)
  , (builtinFloat              |-> builtinPostulate tset)
  , (builtinChar               |-> builtinPostulate tset)
  , (builtinString             |-> builtinPostulate tset)
  , (builtinQName              |-> builtinPostulate tset)
  , (builtinIO                 |-> builtinPostulate (tset --> tset))
  , (builtinAgdaSort           |-> BuiltinData tset [builtinAgdaSortSet, builtinAgdaSortLit, builtinAgdaSortUnsupported])
  , (builtinAgdaType           |-> BuiltinData tset [builtinAgdaTypeEl])
  , (builtinAgdaTerm           |-> BuiltinData tset
                                     [builtinAgdaTermVar, builtinAgdaTermLam
                                     ,builtinAgdaTermDef, builtinAgdaTermCon
                                     ,builtinAgdaTermPi, builtinAgdaTermSort
                                     ,builtinAgdaTermUnsupported])
  , (builtinEquality           |-> BuiltinData (hPi "a" (el primLevel) $
                                                hPi "A" (return $ sort $ varSort 0) $
                                                (El (varSort 1) <$> varM 0) -->
                                                (El (varSort 1) <$> varM 0) -->
                                                return (sort $ varSort 1))
                                               [builtinRefl])
  , (builtinHiding             |-> BuiltinData tset [builtinHidden, builtinInstance, builtinVisible])
  , (builtinRelevance          |-> BuiltinData tset [builtinRelevant, builtinIrrelevant])
  , (builtinRefl               |-> BuiltinDataCons (hPi "a" (el primLevel) $ hPi "A" (return $ sort $ varSort 0) $
                                                    hPi "x" (El (varSort 1) <$> varM 0) $
                                                    El (varSort 2) <$> primEquality <#> varM 2 <#> varM 1 <@> varM 0 <@> varM 0))
  , (builtinNil                |-> BuiltinDataCons (hPi "A" tset (el (list v0))))
  , (builtinCons               |-> BuiltinDataCons (hPi "A" tset (tv0 --> el (list v0) --> el (list v0))))
  , (builtinZero               |-> BuiltinDataCons tnat)
  , (builtinSuc                |-> BuiltinDataCons (tnat --> tnat))
  , (builtinTrue               |-> BuiltinDataCons tbool)
  , (builtinFalse              |-> BuiltinDataCons tbool)
  , (builtinArgArg             |-> BuiltinDataCons (hPi "A" tset (targinfo --> tv0 --> targ tv0)))
  , (builtinArgArgInfo         |-> BuiltinDataCons (thiding --> trelevance --> targinfo))
  , (builtinAgdaTypeEl         |-> BuiltinDataCons (tsort --> tterm --> ttype))
  , (builtinAgdaTermVar        |-> BuiltinDataCons (tnat --> targs --> tterm))
  , (builtinAgdaTermLam        |-> BuiltinDataCons (thiding --> tterm --> tterm))
  , (builtinAgdaTermDef        |-> BuiltinDataCons (tqname --> targs --> tterm))
  , (builtinAgdaTermCon        |-> BuiltinDataCons (tqname --> targs --> tterm))
  , (builtinAgdaTermPi         |-> BuiltinDataCons (targ ttype --> ttype --> tterm))
  , (builtinAgdaTermSort       |-> BuiltinDataCons (tsort --> tterm))
  , (builtinAgdaTermUnsupported|-> BuiltinDataCons tterm)
  , (builtinHidden             |-> BuiltinDataCons thiding)
  , (builtinInstance           |-> BuiltinDataCons thiding)
  , (builtinVisible            |-> BuiltinDataCons thiding)
  , (builtinRelevant           |-> BuiltinDataCons trelevance)
  , (builtinIrrelevant         |-> BuiltinDataCons trelevance)
  , (builtinSize               |-> builtinPostulate tset)
  , (builtinSizeLt             |-> builtinPostulate (tsize --> tset))
  , (builtinSizeSuc            |-> builtinPostulate (tsize --> tsize))
  , (builtinSizeInf            |-> builtinPostulate tsize)
  -- postulate max : {i : Size} -> Size< i -> Size< i -> Size< i
  , (builtinSizeMax            |-> builtinPostulate (tsize --> tsize --> tsize))
     -- (hPi "i" tsize $ let a = el $ primSizeLt <@> v0 in (a --> a --> a)))
  -- postulate .irrelevant : {a : Level}{A : Set a} -> .A -> A
  , (builtinIrrAxiom           |-> BuiltinPostulate Irrelevant
                                     (hPi "a" (el primLevel) $ hPi "A" (return $ sort $ varSort 0) $
                                      (El (varSort 1) <$> varM 0) .--> (El (varSort 1) <$> varM 0)))
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
  , (builtinAgdaFunDef                |-> builtinPostulate tset) -- internally this is QName
  , (builtinAgdaDataDef               |-> builtinPostulate tset) -- internally this is QName
  , (builtinAgdaRecordDef             |-> builtinPostulate tset) -- internally this is QName
  , (builtinAgdaDefinition            |-> BuiltinData tset [builtinAgdaDefinitionFunDef
                                                           ,builtinAgdaDefinitionDataDef
                                                           ,builtinAgdaDefinitionDataConstructor
                                                           ,builtinAgdaDefinitionRecordDef
                                                           ,builtinAgdaDefinitionPostulate
                                                           ,builtinAgdaDefinitionPrimitive])
  , (builtinAgdaDefinitionFunDef          |-> BuiltinDataCons (tfun --> tdefn))
  , (builtinAgdaDefinitionDataDef         |-> BuiltinDataCons (tdtype --> tdefn))
  , (builtinAgdaDefinitionDataConstructor |-> BuiltinDataCons tdefn)
  , (builtinAgdaDefinitionRecordDef       |-> BuiltinDataCons (trec --> tdefn))
  , (builtinAgdaDefinitionPostulate       |-> BuiltinDataCons tdefn)
  , (builtinAgdaDefinitionPrimitive       |-> BuiltinDataCons tdefn)
  ]
  where
        (|->) = (,)

        v0 = varM 0
        v1 = varM 1

        tv0,tv1 :: TCM Type
        tv0 = el v0
        tv1 = el v1

        arg :: TCM Term -> TCM Term
        arg t = primArg <@> t

        targ x     = el (arg (fmap unEl x))
        targs      = el (list (arg primAgdaTerm))
        tterm      = el primAgdaTerm
        tqname     = el primQName
        tnat       = el primNat
        tsize      = el primSize
        tbool      = el primBool
        thiding    = el primHiding
        trelevance = el primRelevance
--        tcolors    = el (list primAgdaTerm) -- TODO guilhem
        targinfo   = el primArgInfo
        ttype      = el primAgdaType
        tsort      = el primAgdaSort
        tdefn      = el primAgdaDefinition
        tfun       = el primAgdaFunDef
        tdtype     = el primAgdaDataDef
        trec       = el primAgdaRecordDef

        verifyPlus plus =
            verify ["n","m"] $ \(@@) zero suc (==) choice -> do
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
            verify ["n","m"] $ \(@@) zero suc (==) choice -> do
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
            verify ["n","m"] $ \(@@) zero suc (==) choice -> do
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
            verify ["k","m","n","j"] $ \(@@) zero suc (==) choice -> do
                let aux k m n j = dsAux @@ k @@ m @@ n @@ j
                    k           = var 0
                    m           = var 1
                    n           = var 2
                    j           = var 3

                aux k m zero    j       == k
                aux k m (suc n) zero    == aux (suc k) m n m
                aux k m (suc n) (suc j) == aux k m n j

        verifyModSucAux dsAux =
            verify ["k","m","n","j"] $ \(@@) zero suc (==) choice -> do
                let aux k m n j = dsAux @@ k @@ m @@ n @@ j
                    k           = var 0
                    m           = var 1
                    n           = var 2
                    j           = var 3

                aux k m zero    j       == k
                aux k m (suc n) zero    == aux zero m n m
                aux k m (suc n) (suc j) == aux (suc k) m n j

        verifyEquals eq =
            verify ["n","m"] $ \(@@) zero suc (===) choice -> do
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
            verify ["n","m"] $ \(@@) zero suc (===) choice -> do
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
                                ([TCM ()] -> TCM ()) -> TCM a) -> TCM a
        verify' pNat pZero pSuc xs f = do
            nat  <- El (mkType 0) <$> pNat
            zero <- pZero
            s    <- pSuc
            let x @@ y = x `apply` [defaultArg y]
                x == y = noConstraints $ equalTerm nat x y
                suc n  = s @@ n
                choice = foldr1 (\x y -> x `catchError` \_ -> y)
            xs <- mapM freshName_ xs
            addCtxs xs (domFromArg $ defaultArg nat) $ f (@@) zero suc (==) choice


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

bindBuiltinInfo :: BuiltinInfo -> A.Expr -> TCM ()
bindBuiltinInfo i (A.ScopedExpr scope e) = setScope scope >> bindBuiltinInfo i e
bindBuiltinInfo (BuiltinInfo s d) e = do
    case d of
      BuiltinData t cs -> do
                           e' <- checkExpr e =<< t
                           let n = length cs
                           inductiveCheck s n e'
                           bindBuiltinName s e'
                           -- NAT and LEVEL must be different. (Why?)
                           when (s `elem` [builtinNat, builtinLevel]) $ do
                             nat   <- getBuiltin' builtinNat
                             level <- getBuiltin' builtinLevel
                             case (nat, level) of
                               (Just nat, Just level) -> do
                                  Def nat   _ <- ignoreSharing <$> normalise nat
                                  Def level _ <- ignoreSharing <$> normalise level
                                  when (nat == level) $ typeError $ GenericError $
                                    builtinNat ++ " and " ++ builtinLevel ++
                                    " have to be different types."
                               _ -> return ()


      BuiltinDataCons t -> do

        let name (Lam h b)  = name (absBody b)
            name (Con c _)  = Con c []
            name (Shared p) = name $ ignoreSharing (derefPtr p)
            name _          = __IMPOSSIBLE__

        e' <- checkExpr e =<< t

        case e of
          A.Con _ -> return ()
          _       -> typeError $ BuiltinMustBeConstructor s e

        bindBuiltinName s (name e')

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
            addConstant qx $ info { theDef = Primitive a pfname (Just cls) mcc }

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
                builtinSizeHook s q e' t'
                bindBuiltinName s e'
              _        -> err
          _ -> err

      BuiltinUnknown mt f -> do
        e' <- maybe (fst <$> inferExpr e) (checkExpr e =<<) mt
        f e'
        bindBuiltinName s e'

-- | Bind a builtin thing to an expression.
bindBuiltin :: String -> A.Expr -> TCM ()
bindBuiltin b e = do
    top <- (== 0) . size <$> getContextTelescope
    unless top $ typeError $ BuiltinInParameterisedModule b
    bind b e
    where
        bind b e
            | b == builtinInf                                   = bindBuiltinInf e
            | b == builtinSharp                                 = bindBuiltinSharp e
            | b == builtinFlat                                  = bindBuiltinFlat e
            | Just i <- find ((==b) . builtinName) coreBuiltins = bindBuiltinInfo i e
            | otherwise                                         = typeError $ NoSuchBuiltinName b
