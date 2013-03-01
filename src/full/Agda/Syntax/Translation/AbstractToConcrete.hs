-- {-# OPTIONS -fwarn-unused-binds #-}
{-# LANGUAGE CPP, PatternGuards, MultiParamTypeClasses, FunctionalDependencies,
             TypeSynonymInstances, FlexibleInstances, UndecidableInstances
  #-}

{-| The translation of abstract syntax to concrete syntax has two purposes.
    First it allows us to pretty print abstract syntax values without having to
    write a dedicated pretty printer, and second it serves as a sanity check
    for the concrete to abstract translation: translating from concrete to
    abstract and then back again should be (more or less) the identity.
-}
module Agda.Syntax.Translation.AbstractToConcrete
    ( ToConcrete(..)
    , toConcreteCtx
    , abstractToConcrete_
    , abstractToConcreteEnv
    , runAbsToCon
    , RangeAndPragma(..)
    , abstractToConcreteCtx
    , withScope
    , makeEnv
    , AbsToCon, DontTouchMe, Env
    , noTakenNames
    ) where

import Control.Applicative
import Control.Monad.Reader
import Data.Char
import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Set as Set
import Data.Set (Set)
import Data.List as List
import qualified Data.Traversable as Trav

import Agda.Syntax.Common hiding (Arg, Dom, NamedArg)
import qualified Agda.Syntax.Common as Common
import Agda.Syntax.Position
import Agda.Syntax.Info
import Agda.Syntax.Internal (MetaId(..))
import Agda.Syntax.Fixity
import Agda.Syntax.Concrete as C
import Agda.Syntax.Concrete.Pretty
import Agda.Syntax.Abstract as A
import Agda.Syntax.Abstract.Views as AV
import Agda.Syntax.Scope.Base

import Agda.TypeChecking.Monad.State (getScope)
import Agda.TypeChecking.Monad.Base  (TCM, NamedMeta(..))
import Agda.TypeChecking.Monad.Options

import Agda.Utils.Maybe
import Agda.Utils.Monad hiding (bracket)
import Agda.Utils.Tuple
import Agda.Utils.Suffix

#include "../../undefined.h"
import Agda.Utils.Impossible

-- Environment ------------------------------------------------------------

data Env = Env { takenNames   :: Set C.Name
               , currentScope :: ScopeInfo
               }

defaultEnv :: Env
defaultEnv = Env { takenNames   = Set.empty
                 , currentScope = emptyScopeInfo
                 }

makeEnv :: ScopeInfo -> Env
makeEnv scope = Env { takenNames   = taken
                    , currentScope = scope
                    }
  where
    ns    = everythingInScope scope
    taken = Set.union vars defs
    vars  = Set.fromList $ map fst $ scopeLocals scope
    defs  = Set.fromList [ x | (x, _) <- Map.toList $ nsNames ns ]

currentPrecedence :: AbsToCon Precedence
currentPrecedence = asks $ scopePrecedence . currentScope

withPrecedence :: Precedence -> AbsToCon a -> AbsToCon a
withPrecedence p = local $ \e ->
  e { currentScope = (currentScope e) { scopePrecedence = p } }

withScope :: ScopeInfo -> AbsToCon a -> AbsToCon a
withScope scope = local $ \e -> e { currentScope = scope }

noTakenNames :: AbsToCon a -> AbsToCon a
noTakenNames = local $ \e -> e { takenNames = Set.empty }

-- The Monad --------------------------------------------------------------

-- | We put the translation into TCM in order to print debug messages.
type AbsToCon = ReaderT Env TCM

runAbsToCon :: AbsToCon c -> TCM c
runAbsToCon m = do
  scope <- getScope
  runReaderT m (makeEnv scope)

abstractToConcreteEnv :: ToConcrete a c => Env -> a -> TCM c
abstractToConcreteEnv flags a = runReaderT (toConcrete a) flags

abstractToConcreteCtx :: ToConcrete a c => Precedence -> a -> TCM c
abstractToConcreteCtx ctx x = do
  scope <- getScope
  let scope' = scope { scopePrecedence = ctx }
  abstractToConcreteEnv (makeEnv scope') x

abstractToConcrete_ :: ToConcrete a c => a -> TCM c
abstractToConcrete_ = runAbsToCon . toConcrete

{-
-- | We make the translation monadic for modularity purposes.
type AbsToCon = Reader Env

runAbsToCon :: AbsToCon a -> TCM a
runAbsToCon m = do
  scope <- getScope
  return $ runReader m (makeEnv scope)

abstractToConcreteEnv :: ToConcrete a c => Env -> a -> TCM c
abstractToConcreteEnv flags a = return $ runReader (toConcrete a) flags

{- Andreas, 2013-02-26 discontinue non-monadic version in favor of debug msg.
abstractToConcrete :: ToConcrete a c => Env -> a -> c
abstractToConcrete flags a = runReader (toConcrete a) flags
-}

abstractToConcreteCtx :: ToConcrete a c => Precedence -> a -> TCM c
abstractToConcreteCtx ctx x = do
  scope <- getScope
  let scope' = scope { scopePrecedence = ctx }
  return $ abstractToConcrete (makeEnv scope') x
  where
    scope = (currentScope defaultEnv) { scopePrecedence = ctx }

abstractToConcrete_ :: ToConcrete a c => a -> TCM c
abstractToConcrete_ x = do
  scope <- getScope
  return $ abstractToConcrete (makeEnv scope) x
-}

-- Dealing with names -----------------------------------------------------

-- | Names in abstract syntax are fully qualified, but the concrete syntax
--   requires non-qualified names in places. In theory (if all scopes are
--   correct), we should get a non-qualified name when translating back to a
--   concrete name, but I suspect the scope isn't always perfect. In these
--   cases we just throw away the qualified part. It's just for pretty printing
--   anyway...
unsafeQNameToName :: C.QName -> C.Name
unsafeQNameToName (C.QName x) = x
unsafeQNameToName (C.Qual _ x) = unsafeQNameToName x

lookupName :: A.Name -> AbsToCon C.Name
lookupName x = do
  names <- asks $ scopeLocals . currentScope
  case lookup x $ map swap names of
      Just y  -> return y
      Nothing -> return $ nameConcrete x
  where
    swap (x, y) = (y, x)

lookupQName :: A.QName -> AbsToCon C.QName
lookupQName x =
    do  scope <- asks currentScope
        case inverseScopeLookupName x scope of
            Just y  -> return y
            Nothing
              | show (qnameToConcrete x) == "_" -> return $ qnameToConcrete x
              | otherwise -> return $ C.Qual (C.Name noRange [Id ""]) $ qnameToConcrete x
                -- this is what happens for names that are not in scope (private names)

lookupModule :: A.ModuleName -> AbsToCon C.QName
lookupModule x =
    do  scope <- asks currentScope
        case inverseScopeLookupModule x scope of
            Just y  -> return y
            Nothing -> return $ mnameToConcrete x
                -- this is what happens for names that are not in scope (private names)

bindName :: A.Name -> (C.Name -> AbsToCon a) -> AbsToCon a
bindName x ret = do
  names <- asks takenNames
  let y = nameConcrete x
  case (Set.member y names) of
    _ | C.isNoName y -> ret y
    True             -> bindName (nextName x) ret
    False            ->
        local (\e -> e { takenNames   = Set.insert y $ takenNames e
                       , currentScope = (currentScope e)
                          { scopeLocals = (y, x) : scopeLocals (currentScope e)
                          }
                       }
              ) $ ret y

-- Dealing with precedences -----------------------------------------------

-- | General bracketing function.
bracket' ::    (e -> e)             -- ^ the bracketing function
            -> (Precedence -> Bool) -- ^ Should we bracket things
                                    --   which have the given
                                    --   precedence?
            -> e -> AbsToCon e
bracket' paren needParen e =
    do  p <- currentPrecedence
        return $ if needParen p then paren e else e

-- | Expression bracketing
bracket :: (Precedence -> Bool) -> AbsToCon C.Expr -> AbsToCon C.Expr
bracket par m =
    do  e <- m
        bracket' (Paren (getRange e)) par e

-- | Pattern bracketing
bracketP_ :: (Precedence -> Bool) -> AbsToCon C.Pattern -> AbsToCon C.Pattern
bracketP_ par m =
    do  e <- m
        bracket' (ParenP (getRange e)) par e

{- UNUSED
-- | Pattern bracketing
bracketP :: (Precedence -> Bool) -> (C.Pattern -> AbsToCon a)
                                 -> ((C.Pattern -> AbsToCon a) -> AbsToCon a)
                                 -> AbsToCon a
bracketP par ret m = m $ \p -> do
    p <- bracket' (ParenP $ getRange p) par p
    ret p
-}

-- Dealing with infix declarations ----------------------------------------

-- | If a name is defined with a fixity that differs from the default, we have
--   to generate a fixity declaration for that name.
withInfixDecl :: DefInfo -> C.Name -> AbsToCon [C.Declaration] -> AbsToCon [C.Declaration]
withInfixDecl i x m = do
  ds <- m
  return $ fixDecl ++ synDecl ++ ds
 where fixDecl = [C.Infix (theFixity $ defFixity i) [x] | theFixity (defFixity i) /= defaultFixity]
       synDecl = [C.Syntax x (theNotation (defFixity i))]

{- UNUSED
withInfixDecls :: [(DefInfo, C.Name)] -> AbsToCon [C.Declaration] -> AbsToCon [C.Declaration]
withInfixDecls = foldr (.) id . map (uncurry withInfixDecl)
-}

-- Dealing with private definitions ---------------------------------------

withAbstractPrivate :: DefInfo -> AbsToCon [C.Declaration] -> AbsToCon [C.Declaration]
withAbstractPrivate i m =
    case (defAccess i, defAbstract i) of
        (PublicAccess, ConcreteDef) -> m
        (p,a)                       ->
            do  ds <- m
                return $ abst a $ priv p $ ds
    where
        priv PrivateAccess ds = [ C.Private (getRange ds) ds ]
        priv _ ds             = ds
        abst AbstractDef ds   = [ C.Abstract (getRange ds) ds ]
        abst _ ds             = ds

-- The To Concrete Class --------------------------------------------------

class ToConcrete a c | a -> c where
    toConcrete :: a -> AbsToCon c
    bindToConcrete :: a -> (c -> AbsToCon b) -> AbsToCon b

    toConcrete     x     = bindToConcrete x return
    bindToConcrete x ret = ret =<< toConcrete x

-- | Translate something in a context of the given precedence.
toConcreteCtx :: ToConcrete a c => Precedence -> a -> AbsToCon c
toConcreteCtx p x = withPrecedence p $ toConcrete x

-- | Translate something in a context of the given precedence.
bindToConcreteCtx :: ToConcrete a c => Precedence -> a -> (c -> AbsToCon b) -> AbsToCon b
bindToConcreteCtx p x ret = withPrecedence p $ bindToConcrete x ret

-- General instances ------------------------------------------------------

instance ToConcrete a c => ToConcrete [a] [c] where
    toConcrete     = mapM toConcrete
    bindToConcrete = thread bindToConcrete

instance (ToConcrete a1 c1, ToConcrete a2 c2) => ToConcrete (a1,a2) (c1,c2) where
    toConcrete (x,y) = liftM2 (,) (toConcrete x) (toConcrete y)
    bindToConcrete (x,y) ret =
        bindToConcrete x $ \x ->
        bindToConcrete y $ \y ->
        ret (x,y)

instance (ToConcrete a1 c1, ToConcrete a2 c2, ToConcrete a3 c3) =>
         ToConcrete (a1,a2,a3) (c1,c2,c3) where
    toConcrete (x,y,z) = reorder <$> toConcrete (x,(y,z))
        where
            reorder (x,(y,z)) = (x,y,z)

    bindToConcrete (x,y,z) ret = bindToConcrete (x,(y,z)) $ ret . reorder
        where
            reorder (x,(y,z)) = (x,y,z)

instance ToConcrete A.ArgInfo C.ArgInfo where
  toConcrete info = do cs <- mapM toConcrete $ argInfoColors info
                       return $ info { argInfoColors = cs }

instance ToConcrete a c => ToConcrete (A.Arg a) (C.Arg c) where
    toConcrete (Common.Arg info x) = liftM2 Common.Arg (toConcrete info) (f x)
      where f = case getHiding info of
                  Hidden    -> toConcreteCtx TopCtx
                  Instance  -> toConcreteCtx TopCtx
                  NotHidden -> toConcrete

    bindToConcrete (Common.Arg info x) ret = do info <- toConcrete info
                                                bindToConcreteCtx (hiddenArgumentCtx $ getHiding info) x $
                                                                  ret . Common.Arg info

instance ToConcrete a c => ToConcrete (Named name a) (Named name c) where
    toConcrete (Named n x) = Named n <$> toConcrete x
    bindToConcrete (Named n x) ret = bindToConcrete x $ ret . Named n

newtype DontTouchMe a = DontTouchMe a

instance ToConcrete (DontTouchMe a) a where
    toConcrete (DontTouchMe x) = return x

-- Names ------------------------------------------------------------------

instance ToConcrete A.Name C.Name where
  toConcrete       = lookupName
  bindToConcrete x = bindName x

instance ToConcrete A.QName C.QName where
  toConcrete = lookupQName

instance ToConcrete A.ModuleName C.QName where
  toConcrete = lookupModule

-- Expression instance ----------------------------------------------------

instance ToConcrete A.Expr C.Expr where
    toConcrete (Var x)            = Ident . C.QName <$> toConcrete x
    toConcrete (Def x)            = Ident <$> toConcrete x
    toConcrete (Con (AmbQ (x:_))) = Ident <$> toConcrete x
    toConcrete (Con (AmbQ []))    = __IMPOSSIBLE__
        -- for names we have to use the name from the info, since the abstract
        -- name has been resolved to a fully qualified name (except for
        -- variables)
    toConcrete (A.Lit l)            = return $ C.Lit l

    toConcrete (A.QuestionMark i)   = return $ C.QuestionMark
                                                (getRange i)
                                                (metaNumber i)
    toConcrete (A.Underscore i)     = return $
      C.Underscore (getRange i) $
       fmap (show . NamedMeta (metaNameSuggestion i) . MetaId) (metaNumber i)

    toConcrete e@(A.App i e1 e2)    =
        tryToRecoverOpApp e
        -- or fallback to App
        $ bracket appBrackets
        $ do e1' <- toConcreteCtx FunctionCtx e1
             e2' <- toConcreteCtx ArgumentCtx e2
             return $ C.App (getRange i) e1' e2'

    toConcrete (A.WithApp i e es) =
      bracket withAppBrackets $ do
        e <- toConcreteCtx WithFunCtx e
        es <- mapM (toConcreteCtx WithArgCtx) es
        return $ C.WithApp (getRange i) e es

    toConcrete (A.AbsurdLam i h) =
      bracket lamBrackets $ return $ C.AbsurdLam (getRange i) h
    toConcrete e@(A.Lam i _ _)      =
        bracket lamBrackets
        $ case lamView e of
            (bs, e) ->
                bindToConcrete (map makeDomainFree bs) $ \bs -> do
                    e  <- toConcreteCtx TopCtx e
                    return $ C.Lam (getRange i) bs e
        where
            lamView (A.Lam _ b@(A.DomainFree _ _) e) =
                case lamView e of
                    ([], e)                        -> ([b], e)
                    (bs@(A.DomainFree _ _ : _), e) -> (b:bs, e)
                    _                              -> ([b], e)
            lamView (A.Lam _ b@(A.DomainFull _) e) =
                case lamView e of
                    ([], e)                        -> ([b], e)
                    (bs@(A.DomainFull _ : _), e)   -> (b:bs, e)
                    _                              -> ([b], e)
            lamView e = ([], e)
    toConcrete (A.ExtendedLam i di qname cs) =
        bracket lamBrackets $ do
          decls <- concat <$> toConcrete cs
              -- we know all lhs are of the form `.extlam p1 p2 ... pn`,
              -- with the name .extlam leftmost. It is our mission to remove it.
          let removeApp (C.RawAppP r (_:es)) = return $ C.RawAppP r es
              removeApp (C.AppP (C.IdentP _) np) = return $ namedArg np
              removeApp (C.AppP p np) = do
                p <- removeApp p
                return $ C.AppP p np
              removeApp p = do
                lift $ reportSLn "extendedlambda" 50 $ "abstractToConcrete removeApp p = " ++ show p
                return p -- __IMPOSSIBLE__ -- Andreas, this is actually not impossible, my strictification exposed this sleeping bug
          let decl2clause (C.FunClause lhs rhs wh) = do
                let p = lhsOriginalPattern lhs
                lift $ reportSLn "extendedlambda" 50 $ "abstractToConcrete extended lambda pattern p = " ++ show p
                p' <- removeApp p
                return (lhs{ lhsOriginalPattern = p' }, rhs, wh)
              decl2clause _ = __IMPOSSIBLE__
          C.ExtendedLam (getRange i) <$> mapM decl2clause decls
    toConcrete (A.Pi _ [] e) = toConcrete e
    toConcrete t@(A.Pi i _ _)  = case piTel t of
      (tel, e) ->
        bracket piBrackets
        $ bindToConcrete tel $ \b' -> do
             e' <- toConcreteCtx TopCtx e
             return $ C.Pi b' e'
      where
        piTel (A.Pi _ tel e) = (tel ++) -*- id $ piTel e
        piTel e              = ([], e)

    toConcrete (A.Fun i a b) =
        bracket piBrackets
        $ do a' <- toConcreteCtx (if irr then DotPatternCtx else FunctionSpaceDomainCtx) a
             b' <- toConcreteCtx TopCtx b
             return $ C.Fun (getRange i) (addRel a' $ mkArg a') b'
        where
            irr        = getRelevance a `elem` [Irrelevant, NonStrict]
            addRel a e = case getRelevance a of
                           Irrelevant -> addDot a e
                           NonStrict  -> addDot a (addDot a e)
                           _          -> e
            addDot a e = Dot (getRange a) e
            mkArg (Common.Arg info e) = case getHiding info of
                                          Hidden    -> HiddenArg   (getRange e) (unnamed e)
                                          Instance  -> InstanceArg (getRange e) (unnamed e)
                                          NotHidden -> e

    toConcrete (A.Set i 0)  = return $ C.Set (getRange i)
    toConcrete (A.Set i n)  = return $ C.SetN (getRange i) n
    toConcrete (A.Prop i)   = return $ C.Prop (getRange i)

    toConcrete (A.Let i ds e) =
        bracket lamBrackets
        $ bindToConcrete ds $ \ds' -> do
             e'  <- toConcreteCtx TopCtx e
             return $ C.Let (getRange i) (concat ds') e'

    toConcrete (A.Rec i fs) =
      bracket appBrackets $ do
        let (xs, es) = unzip fs
        es <- toConcreteCtx TopCtx es
        return $ C.Rec (getRange i) $ zip xs es

    toConcrete (A.RecUpdate i e fs) =
      bracket appBrackets $ do
        let (xs, es) = unzip fs
        e <- toConcrete e
        es <- toConcreteCtx TopCtx es
        return $ C.RecUpdate (getRange i) e $ zip xs es

    toConcrete (A.ETel tel) = do
      tel <- toConcrete tel
      return $ C.ETel tel

    toConcrete (A.ScopedExpr _ e) = toConcrete e

    toConcrete (A.QuoteGoal i x e) =
      bracket lamBrackets $
        bindToConcrete x $ \ x' -> do
            e' <- toConcrete e
            return $ C.QuoteGoal (getRange i) x' e'
    toConcrete (A.Quote i) = return $ C.Quote (getRange i)
    toConcrete (A.QuoteTerm i) = return $ C.QuoteTerm (getRange i)
    toConcrete (A.Unquote i) = return $ C.Unquote (getRange i)

    -- Andreas, 2012-04-02: TODO!  print DontCare as irrAxiom
    -- Andreas, 2010-10-05 print irrelevant things as ordinary things
    toConcrete (A.DontCare e) = C.Dot r . C.Paren r  <$> toConcrete e
       where r = getRange e
--    toConcrete (A.DontCare e) = C.DontCare <$> toConcreteCtx TopCtx e
{-
    -- Andreas, 2010-09-21 abuse C.Underscore to print irrelevant things
    toConcrete (A.DontCare) = return $ C.Underscore noRange Nothing
-}
    toConcrete (A.PatternSyn n) = C.Ident <$> toConcrete n

makeDomainFree :: A.LamBinding -> A.LamBinding
makeDomainFree b@(A.DomainFull (A.TypedBindings r (Common.Arg info (A.TBind _ [x] t)))) =
  case unScope t of
    A.Underscore MetaInfo{metaNumber = Nothing} -> A.DomainFree info x
    _ -> b
  where
    unScope (A.ScopedExpr _ e) = unScope e
    unScope e = e
makeDomainFree b = b

-- Binder instances -------------------------------------------------------

instance ToConcrete A.LamBinding C.LamBinding where
    bindToConcrete (A.DomainFree info x) ret = do info <- toConcrete info
                                                  bindToConcrete x $ ret . C.DomainFree info . mkBoundName_
    bindToConcrete (A.DomainFull b)      ret = bindToConcrete b $ ret . C.DomainFull

instance ToConcrete A.TypedBindings C.TypedBindings where
    bindToConcrete (A.TypedBindings r bs) ret =
        bindToConcrete bs $ \bs ->
        ret (C.TypedBindings r bs)

instance ToConcrete A.TypedBinding C.TypedBinding where
    bindToConcrete (A.TBind r xs e) ret =
        bindToConcrete xs $ \xs -> do
        e <- toConcreteCtx TopCtx e
        ret (C.TBind r (map mkBoundName_ xs) e)
    bindToConcrete (A.TNoBind e) ret = do
        e <- toConcreteCtx TopCtx e
        ret (C.TNoBind e)

instance ToConcrete LetBinding [C.Declaration] where
    bindToConcrete (LetBind i info x t e) ret =
        bindToConcrete x $ \x ->
        do (t,(e, [], [], [])) <- toConcrete (t, A.RHS e)
           info <- toConcrete info
           ret [ C.TypeSig info x t
               , C.FunClause (C.LHS (C.IdentP $ C.QName x) [] [] [])
                             e C.NoWhere
               ]
    -- TODO: bind variables
    bindToConcrete (LetPatBind i p e) ret = do
        p <- toConcrete p
        e <- toConcrete e
        ret [ C.FunClause (C.LHS p [] [] []) (C.RHS e) NoWhere ]
    bindToConcrete (LetApply i x modapp _ _) ret = do
      x' <- unqualify <$> toConcrete x
      modapp <- toConcrete modapp
      let r = getRange modapp
          open = maybe DontOpen id $ minfoOpenShort i
          dir  = maybe defaultImportDir{ importDirRange = r } id $ minfoDirective i
      -- This is no use since toAbstract LetDefs is in localToAbstract.
      local (openModule' x dir id) $
        ret [ C.ModuleMacro (getRange i) x' modapp open dir ]
    bindToConcrete (LetOpen i x) ret = do
      x' <- toConcrete x
      let dir = maybe defaultImportDir id $ minfoDirective i
      local (openModule' x dir restrictPrivate) $
            ret [ C.Open (getRange i) x' dir ]

data AsWhereDecls = AsWhereDecls [A.Declaration]

instance ToConcrete AsWhereDecls WhereClause where
  bindToConcrete (AsWhereDecls []) ret = ret C.NoWhere
  bindToConcrete (AsWhereDecls ds@[Section _ am _ _]) ret = do
    ds' <- declsToConcrete ds
    cm  <- unqualify <$> lookupModule am
    let wh' = (if isNoName cm then AnyWhere else SomeWhere cm) $ ds'
    local (openModule' am defaultImportDir id) $ ret wh'
  bindToConcrete (AsWhereDecls ds) ret =
    ret . AnyWhere =<< declsToConcrete ds

mergeSigAndDef :: [C.Declaration] -> [C.Declaration]
mergeSigAndDef (C.RecordSig _ x bs e : C.Record r y ind c _ Nothing fs : ds)
  | x == y = C.Record r y ind c bs (Just e) fs : mergeSigAndDef ds
mergeSigAndDef (C.DataSig _ _ x bs e : C.Data r i y _ Nothing cs : ds)
  | x == y = C.Data r i y bs (Just e) cs : mergeSigAndDef ds
mergeSigAndDef (d : ds) = d : mergeSigAndDef ds
mergeSigAndDef [] = []

openModule' :: A.ModuleName -> ImportDirective -> (Scope -> Scope) -> Env -> Env
openModule' x dir restrict env = env{currentScope = sInfo{scopeModules = mods'}}
  where sInfo = currentScope env
        amod  = scopeCurrent sInfo
        mods  = scopeModules sInfo
        news  = setScopeAccess PrivateNS
                $ applyImportDirective dir
                $ maybe emptyScope restrict
                $ Map.lookup x mods
        mods' = Map.update (Just . (`mergeScope` news)) amod mods


-- Declaration instances --------------------------------------------------

declsToConcrete :: [A.Declaration] -> AbsToCon [C.Declaration]
declsToConcrete ds = mergeSigAndDef . concat <$> toConcrete ds

instance ToConcrete A.RHS (C.RHS, [C.Expr], [C.Expr], [C.Declaration]) where
    toConcrete (A.RHS e) = do
      e <- toConcrete e
      return (C.RHS e, [], [], [])
    toConcrete A.AbsurdRHS = return (C.AbsurdRHS, [], [], [])
    toConcrete (A.WithRHS _ es cs) = do
      es <- toConcrete es
      cs <- concat <$> toConcrete cs
      return (C.AbsurdRHS, [], es, cs)
    toConcrete (A.RewriteRHS _ eqs rhs wh) = do
      wh <- declsToConcrete wh
      (rhs, eqs', es, whs) <- toConcrete rhs
      unless (null eqs')
        __IMPOSSIBLE__
      eqs <- toConcrete eqs
      return (rhs, eqs, es, wh ++ whs)

instance ToConcrete (Maybe A.QName) (Maybe C.Name) where
  toConcrete Nothing = return Nothing
  toConcrete (Just x) = do
    x' <- toConcrete (qnameName x)
    return $ Just x'

{- UNUSED
-- | Helper function used in instance @ToConcrete Definition@.
telToTypedBindingss :: [C.LamBinding] -> [C.TypedBindings]
telToTypedBindingss = map lamBindingToTypedBindings where

  lamBindingToTypedBindings :: C.LamBinding -> C.TypedBindings
  lamBindingToTypedBindings b =
    case b of
      C.DomainFull t     -> t
      C.DomainFree info n -> C.TypedBindings noRange $
        Common.Arg info $ C.TBind noRange [n] $ C.Underscore noRange Nothing
-}

instance ToConcrete (Constr A.Constructor) C.Declaration where
  toConcrete (Constr (A.ScopedDecl scope [d])) =
    withScope scope $ toConcrete (Constr d)
  toConcrete (Constr (A.Axiom i info x t)) = do
    x' <- unsafeQNameToName <$> toConcrete x
    t' <- toConcreteCtx TopCtx t
    info <- toConcrete info
    return $ C.TypeSig info x' t'
  toConcrete (Constr d) = head <$> toConcrete d

instance ToConcrete A.Clause [C.Declaration] where
  toConcrete (A.Clause lhs rhs wh) =
      bindToConcrete lhs $ \lhs ->
        case lhs of
          C.LHS p wps _ _ -> do
            bindToConcrete (AsWhereDecls wh)  $ \wh' -> do
                (rhs', eqs, with, wcs) <- toConcreteCtx TopCtx rhs
                return $ FunClause (C.LHS p wps eqs with) rhs' wh' : wcs
          C.Ellipsis {} -> __IMPOSSIBLE__
          -- TODO: Is the case above impossible? Previously there was
          -- no code for it, but GHC 7's completeness checker spotted
          -- that the case was not covered.

instance ToConcrete A.ModuleApplication C.ModuleApplication where
  toConcrete (A.SectionApp tel y es) = do
    y  <- toConcrete y
    bindToConcrete tel $ \tel -> do
    es <- toConcrete es
    let r = fuseRange y es
    return $ C.SectionApp r tel (foldl (C.App r) (C.Ident y) es)
  toConcrete (A.RecordModuleIFS rec) = do
    rec <- toConcrete rec
    return $ C.RecordModuleIFS (getRange rec) rec

instance ToConcrete A.Declaration [C.Declaration] where
  toConcrete (ScopedDecl scope ds) =
    withScope scope (declsToConcrete ds)

  toConcrete (Axiom i info x t) = do
    x' <- unsafeQNameToName <$> toConcrete x
    withAbstractPrivate i $
      withInfixDecl i x'  $ do
      t' <- toConcreteCtx TopCtx t
      info <- toConcrete info
      return [C.Postulate (getRange i) [C.TypeSig info x' t']]

  toConcrete (A.Field i x t) = do
    x' <- unsafeQNameToName <$> toConcrete x
    withAbstractPrivate i $
      withInfixDecl i x'  $ do
      t' <- toConcreteCtx TopCtx t
      return [C.Field x' t']

  toConcrete (A.Primitive i x t) = do
    x' <- unsafeQNameToName <$> toConcrete x
    withAbstractPrivate i $
      withInfixDecl i x'  $ do
      t' <- toConcreteCtx TopCtx t
      return [C.Primitive (getRange i) [C.TypeSig defaultArgInfo x' t']]
        -- Primitives are always relevant.

  toConcrete (A.FunDef i _ _ cs) =
    withAbstractPrivate i $ concat <$> toConcrete cs

  toConcrete (A.DataSig i x bs t) =
    withAbstractPrivate i $
    bindToConcrete bs $ \tel' -> do
      x' <- unsafeQNameToName <$> toConcrete x
      t' <- toConcreteCtx TopCtx t
      return [ C.DataSig (getRange i) Inductive x' (map C.DomainFull tel') t' ]

  toConcrete (A.DataDef i x bs cs) =
    withAbstractPrivate i $
    bindToConcrete (map makeDomainFree bs) $ \tel' -> do
      (x',cs') <- (unsafeQNameToName -*- id) <$> toConcrete (x, map Constr cs)
      return [ C.Data (getRange i) Inductive x' tel' Nothing cs' ]

  toConcrete (A.RecSig i x bs t) =
    withAbstractPrivate i $
    bindToConcrete bs $ \tel' -> do
      x' <- unsafeQNameToName <$> toConcrete x
      t' <- toConcreteCtx TopCtx t
      return [ C.RecordSig (getRange i) x' (map C.DomainFull tel') t' ]

  toConcrete (A.RecDef  i x ind c bs t cs) =
    withAbstractPrivate i $
    bindToConcrete (map makeDomainFree bs) $ \tel' -> do
      (x',cs') <- (unsafeQNameToName -*- id) <$> toConcrete (x, map Constr cs)
      return [ C.Record (getRange i) x' ind Nothing tel' Nothing cs' ]

  toConcrete (A.Mutual i ds) = declsToConcrete ds

  toConcrete (A.Section i x tel ds) = do
    x <- toConcrete x
    bindToConcrete tel $ \tel -> do
    ds <- declsToConcrete ds
    return [ C.Module (getRange i) x tel ds ]

  toConcrete (A.Apply i x modapp _ _) = do
    x  <- unsafeQNameToName <$> toConcrete x
    modapp <- toConcrete modapp
    let r = getRange modapp
        open = maybe DontOpen id $ minfoOpenShort i
        dir  = maybe defaultImportDir{ importDirRange = r } id $ minfoDirective i
    return [ C.ModuleMacro (getRange i) x modapp open dir ]

  toConcrete (A.Import i x) = do
    x <- toConcrete x
    let open = maybe DontOpen id $ minfoOpenShort i
        dir  = maybe defaultImportDir id $ minfoDirective i
    return [ C.Import (getRange i) x Nothing open dir]

  toConcrete (A.Pragma i p)     = do
    p <- toConcrete $ RangeAndPragma (getRange i) p
    return [C.Pragma p]

  toConcrete (A.Open i x) = do
    x <- toConcrete x
    return [C.Open (getRange i) x defaultImportDir]


data RangeAndPragma = RangeAndPragma Range A.Pragma

instance ToConcrete RangeAndPragma C.Pragma where
    toConcrete (RangeAndPragma r p) = case p of
        A.OptionsPragma xs  -> return $ C.OptionsPragma r xs
        A.BuiltinPragma b x -> do
          x <- toConcrete x
          return $ C.BuiltinPragma r b x
        A.CompiledTypePragma x hs -> do
          x <- toConcrete x
          return $ C.CompiledTypePragma r x hs
        A.CompiledDataPragma x hs hcs -> do
          x <- toConcrete x
          return $ C.CompiledDataPragma r x hs hcs
        A.CompiledPragma x hs -> do
          x <- toConcrete x
          return $ C.CompiledPragma r x hs
        A.CompiledEpicPragma x e -> do
          x <- toConcrete x
          return $ C.CompiledEpicPragma r x e
        A.CompiledJSPragma x e -> do
          x <- toConcrete x
          return $ C.CompiledJSPragma r x e
        A.StaticPragma x -> do
            x <- toConcrete x
            return $ C.StaticPragma r x
        A.EtaPragma x -> C.EtaPragma r <$> toConcrete x

-- Left hand sides --------------------------------------------------------

noImplicitArgs = filter (noImplicit . namedArg)
noImplicitPats = filter noImplicit

noImplicit (A.ImplicitP _) = False
noImplicit _               = True

instance ToConcrete A.LHS C.LHS where
    bindToConcrete (A.LHS i lhscore wps) ret = do
      bindToConcreteCtx TopCtx lhscore $ \lhs ->
        bindToConcreteCtx TopCtx (noImplicitPats wps) $ \wps ->
          ret $ C.LHS lhs wps [] []
{-
    bindToConcrete (A.LHS i (A.LHSHead x args) wps) ret = do
      bindToConcreteCtx TopCtx (A.DefP info x args) $ \lhs ->
        bindToConcreteCtx TopCtx (noImplicitPats wps) $ \wps ->
          ret $ C.LHS lhs wps [] []
      where info = PatRange (getRange i)
-}

instance ToConcrete A.LHSCore C.Pattern where
    bindToConcrete = bindToConcrete . lhsCoreToPattern
{-
    bindToConcrete (A.LHSHead x args) ret = do
      bindToConcreteCtx TopCtx (A.DefP info x args) $ \ lhs ->
        ret $ lhs
      where info = PatRange noRange -- seems to be unused anyway
    bindToConcrete (A.LHSProj d ps1 lhscore ps2) ret = do
      d <- toConcrete d
      bindToConcrete ps1 $ \ ps1 ->
        bindToConcrete lhscore $ \ p ->
          bindToConcrete ps2 $ \ ps2 ->
            ret $ makePattern d ps1 p ps2
  -}

appBrackets' :: [arg] -> Precedence -> Bool
appBrackets' []    _   = False
appBrackets' (_:_) ctx = appBrackets ctx

-- TODO: bind variables properly
instance ToConcrete A.Pattern C.Pattern where
    toConcrete (VarP x)    = toConcrete x >>= return . IdentP . C.QName
    toConcrete (A.WildP i)         =
        return $ C.WildP (getRange i)
    toConcrete (ConP i (AmbQ []) args) = __IMPOSSIBLE__
    toConcrete p@(ConP i (AmbQ (x:_)) args) =
      tryToRecoverOpAppP p $
        bracketP_ (appBrackets' args) $ do
            x <- toConcrete x
            args <- toConcreteCtx ArgumentCtx (noImplicitArgs args)
            return $ foldl AppP (C.IdentP x) args
    toConcrete p@(DefP i x args) =
      tryToRecoverOpAppP p $
        bracketP_ (appBrackets' args) $ do
            x <- toConcrete x
            args <- toConcreteCtx ArgumentCtx (noImplicitArgs args)
            return $ foldl AppP (C.IdentP x) args
    toConcrete (A.AsP i x p)   = do
      (x, p) <- toConcreteCtx ArgumentCtx (x,p)
      return $ C.AsP (getRange i) x p
    toConcrete (A.AbsurdP i) = return $ C.AbsurdP (getRange i)
    toConcrete (A.LitP l)    = return $ C.LitP l
    toConcrete (A.DotP i e)  = do
        e <- toConcreteCtx DotPatternCtx e
        return $ C.DotP (getRange i) e
    -- just for debugging purposes (shouldn't show up in practise)
    toConcrete (A.ImplicitP i) = return $ C.IdentP (C.QName $ C.Name noRange [C.Id "(implicit)"])
    toConcrete (A.PatternSynP i n _) = IdentP <$> toConcrete n


-- Helpers for recovering C.OpApp ------------------------------------------

data Hd = HdVar A.Name | HdCon A.QName | HdDef A.QName

cOpApp :: Range -> C.QName -> [C.Expr] -> C.Expr
cOpApp r n es = C.OpApp r n (map Ordinary es)

tryToRecoverOpApp :: A.Expr -> AbsToCon C.Expr -> AbsToCon C.Expr
tryToRecoverOpApp e def = recoverOpApp bracket cOpApp view e def
  where
    view e = case AV.appView e of
      --NonApplication _   -> Nothing
      Application (Var x) args -> Just (HdVar x, args)
      Application (Def f) args -> Just (HdDef f, args)
      Application (Con (AmbQ (c:_))) args -> Just (HdCon c, args)
      Application (Con (AmbQ [])) args -> __IMPOSSIBLE__
      _ -> Nothing

tryToRecoverOpAppP :: A.Pattern -> AbsToCon C.Pattern -> AbsToCon C.Pattern
tryToRecoverOpAppP p def = recoverOpApp bracketP_ C.OpAppP view p def
  where
    view p = case p of
      ConP _ (AmbQ (c:_)) ps -> Just (HdCon c, ps)
      DefP _ f            ps -> Just (HdDef f, ps)
      _                      -> Nothing

recoverOpApp :: (ToConcrete a c, HasRange c)
  => ((Precedence -> Bool) -> AbsToCon c -> AbsToCon c)
  -> (Range -> C.QName -> [c] -> c)
  -> (a -> Maybe (Hd, [A.NamedArg a]))
  -> a
  -> AbsToCon c
  -> AbsToCon c
recoverOpApp bracket opApp view e mDefault = case view e of
  Nothing -> mDefault
  Just (hd, args)
    | all notHidden args  -> do
      let  args' = map namedArg args
      case hd of
        HdVar  n
          | isNoName n    -> mDefault
          | otherwise     -> doQNameHelper id        C.QName  n args'
        HdDef qn          -> doQNameHelper qnameName id      qn args'
        HdCon qn          -> doQNameHelper qnameName id      qn args'
    | otherwise           -> mDefault
  where

  isNoName :: A.Name -> Bool
  isNoName = C.isNoName . A.nameConcrete

{- RETIRED
  notHidden :: A.NamedArg a -> Bool
  notHidden = notHidden . argInfo
-}

  doQNameHelper fixityHelper conHelper n as = do
    x <- toConcrete n
    doQName (theFixity $ nameFixity $ fixityHelper n) (conHelper x) as

  -- fall-back (wrong number of arguments or no holes)
  doQName _ n es
    | length xs == 1        = mDefault
    | length es /= numHoles = mDefault
    | List.null es          = mDefault
    where
      xs       = C.nameParts $ C.unqualify n
      numHoles = length (filter (== Hole) xs)
{- UNUSED
      msg      = concat [ "doQName "
                        , showList xs ""
                        , " on "
                        , show (length es)
                        , " args" ]
-}

  -- binary case
  doQName fixity n as
    | Hole <- head xs
    , Hole <- last xs = do
        let a1  = head as
            an  = last as
            as' = case as of
                    as@(_ : _ : _) -> init $ tail as
                    _              -> __IMPOSSIBLE__
        e1 <- toConcreteCtx (LeftOperandCtx fixity) a1
        es <- mapM (toConcreteCtx InsideOperandCtx) as'
        en <- toConcreteCtx (RightOperandCtx fixity) an
        bracket (opBrackets fixity)
          $ return $ opApp (getRange (e1, en)) n ([e1] ++ es ++ [en])
    where
      xs = C.nameParts $ C.unqualify n

  -- prefix
  doQName fixity n as
    | Hole <- last xs = do
        let an  = last as
            as' = case as of
                    as@(_ : _) -> init as
                    _          -> __IMPOSSIBLE__
        es <- mapM (toConcreteCtx InsideOperandCtx) as'
        en <- toConcreteCtx (RightOperandCtx fixity) an
        bracket (opBrackets fixity)
          $ return $ opApp (getRange (n, en)) n (es ++ [en])
    where
      xs = C.nameParts $ C.unqualify n

  -- postfix
  doQName fixity n as
    | Hole <- head xs = do
        let a1  = head as
            as' = tail as
        e1 <- toConcreteCtx (LeftOperandCtx fixity) a1
        es <- mapM (toConcreteCtx InsideOperandCtx) as'
        bracket (opBrackets fixity)
          $ return $ opApp (getRange (e1, n)) n ([e1] ++ es)
    where
      xs = C.nameParts $ C.unqualify n

  -- roundfix
  doQName _ n as = do
    es <- mapM (toConcreteCtx InsideOperandCtx) as
    bracket roundFixBrackets
      $ return $ opApp (getRange n) n es
