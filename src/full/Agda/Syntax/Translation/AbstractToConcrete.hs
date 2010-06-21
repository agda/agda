{-# LANGUAGE CPP, PatternGuards, MultiParamTypeClasses, FunctionalDependencies,
             TypeSynonymInstances, FlexibleInstances, UndecidableInstances,
             OverlappingInstances
  #-}

{-| The translation of abstract syntax to concrete syntax has two purposes.
    First it allows us to pretty print abstract syntax values without having to
    write a dedicated pretty printer, and second it serves as a sanity check
    for the concrete to abstract translation: translating from concrete to
    abstract and then back again should be (more or less) the identity.
-}
module Agda.Syntax.Translation.AbstractToConcrete
    ( ToConcrete(..)
    , abstractToConcrete_
    , runAbsToCon
    , RangeAndPragma(..)
    , abstractToConcreteCtx
    , withScope
    , makeEnv
    , abstractToConcrete
    , AbsToCon, TypeAndDef, DontTouchMe, Env
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

import Agda.Syntax.Common
import Agda.Syntax.Position
import Agda.Syntax.Info
import Agda.Syntax.Fixity
import Agda.Syntax.Concrete as C
import Agda.Syntax.Concrete.Pretty
import Agda.Syntax.Abstract as A
import Agda.Syntax.Abstract.Views as AV
import Agda.Syntax.Scope.Base

import Agda.TypeChecking.Monad.State (getScope)
import Agda.TypeChecking.Monad.Base  (MonadTCM)

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

-- The Monad --------------------------------------------------------------

-- | We make the translation monadic for modularity purposes.
type AbsToCon = Reader Env

runAbsToCon :: MonadTCM tcm => AbsToCon a -> tcm a
runAbsToCon m = do
  scope <- getScope
  return $ runReader m (makeEnv scope)

abstractToConcrete :: ToConcrete a c => Env -> a -> c
abstractToConcrete flags a = runReader (toConcrete a) flags

abstractToConcreteCtx :: (MonadTCM tcm, ToConcrete a c) => Precedence -> a -> tcm c
abstractToConcreteCtx ctx x = do
  scope <- getScope
  let scope' = scope { scopePrecedence = ctx }
  return $ abstractToConcrete (makeEnv scope') x
  where
    scope = (currentScope defaultEnv) { scopePrecedence = ctx }

abstractToConcrete_ :: (MonadTCM tcm, ToConcrete a c) => a -> tcm c
abstractToConcrete_ x = do
  scope <- getScope
  return $ abstractToConcrete (makeEnv scope) x

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
            Nothing -> return $ C.Qual (C.Name noRange [Id ""]) $ qnameToConcrete x
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
            -> (Precedence -> Bool) -- ^ do we need brackets
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

-- | Pattern bracketing
bracketP :: (Precedence -> Bool) -> (C.Pattern -> AbsToCon a)
                                 -> ((C.Pattern -> AbsToCon a) -> AbsToCon a)
                                 -> AbsToCon a
bracketP par ret m = m $ \p -> do
    p <- bracket' (ParenP $ getRange p) par p
    ret p

-- Dealing with infix declarations ----------------------------------------

-- | If a name is defined with a fixity that differs from the default, we have
--   to generate a fixity declaration for that name.
withInfixDecl :: DefInfo -> C.Name -> AbsToCon [C.Declaration] -> AbsToCon [C.Declaration]
withInfixDecl i x m
    | defFixity i == defaultFixity = m
    | otherwise                    = do
        ds <- m
        return $ C.Infix (defFixity i) [x] : ds

withInfixDecls :: [(DefInfo, C.Name)] -> AbsToCon [C.Declaration] -> AbsToCon [C.Declaration]
withInfixDecls = foldr (.) id . map (uncurry withInfixDecl)

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

instance ToConcrete a c => ToConcrete (Arg a) (Arg c) where
    toConcrete (Arg h@Hidden    x) = Arg h <$> toConcreteCtx TopCtx x
    toConcrete (Arg h@NotHidden x) = Arg h <$> toConcrete x

    bindToConcrete (Arg h x) ret = bindToConcreteCtx (hiddenArgumentCtx h) x $ ret . Arg h

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
    toConcrete (A.Underscore i)     = return $ C.Underscore
                                                (getRange i)
                                                (metaNumber i)

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
                bindToConcrete bs $ \bs -> do
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
        $ do a' <- toConcreteCtx FunctionSpaceDomainCtx a
             b' <- toConcreteCtx TopCtx b
             return $ C.Fun (getRange i) (mkArg a') b'
        where
            mkArg (Arg Hidden    e) = HiddenArg (getRange e) (unnamed e)
            mkArg (Arg NotHidden e) = e

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

    toConcrete (A.ETel tel) = do
      tel <- toConcrete tel
      return $ C.ETel tel

    toConcrete (A.ScopedExpr _ e) = toConcrete e

    toConcrete (A.QuoteGoal i x e) =
      bracket lamBrackets $
        bindToConcrete x $ \ x' -> do
            e' <- toConcrete e
            return $ C.QuoteGoal (getRange i) x' e'
    toConcrete (A.Quote i x) =
      bracket appBrackets $ do
        C.Ident x' <- toConcrete x
        return $ C.Quote (getRange i) x'

-- Binder instances -------------------------------------------------------

instance ToConcrete A.LamBinding C.LamBinding where
    bindToConcrete (A.DomainFree h x) ret = bindToConcrete x $ ret . C.DomainFree h . mkBoundName_
    bindToConcrete (A.DomainFull b)   ret = bindToConcrete b $ ret . C.DomainFull

instance ToConcrete A.TypedBindings C.TypedBindings where
    bindToConcrete (A.TypedBindings r h bs) ret =
        bindToConcrete bs $ \bs ->
        ret (C.TypedBindings r h bs)

instance ToConcrete A.TypedBinding C.TypedBinding where
    bindToConcrete (A.TBind r xs e) ret =
        bindToConcrete xs $ \xs -> do
        e <- toConcreteCtx TopCtx e
        ret (C.TBind r (map mkBoundName_ xs) e)
    bindToConcrete (A.TNoBind e) ret = do
        e <- toConcreteCtx TopCtx e
        ret (C.TNoBind e)

instance ToConcrete LetBinding [C.Declaration] where
    bindToConcrete (LetBind i x t e) ret =
        bindToConcrete x $ \x ->
        do  (t,(e, [], [], [])) <- toConcrete (t, A.RHS e)
            ret [ C.TypeSig x t
                , C.FunClause (C.LHS (C.IdentP $ C.QName x) [] [] [])
                              e C.NoWhere
                ]
    bindToConcrete (LetApply i x tel y es _ _) ret = do
      x  <- unsafeQNameToName <$> toConcrete x
      y  <- toConcrete y
      bindToConcrete tel $ \tel -> do
      es <- toConcrete es
      let r = fuseRange y es
      ret [ C.ModuleMacro (getRange i) x tel
                  (foldl (C.App r) (C.Ident y) es) DontOpen
                  (ImportDirective r (Hiding []) [] False)
          ]
    bindToConcrete (LetOpen i x dir) ret = do
      y <- toConcrete x
      local openModule_x $ ret [ C.Open (getRange i) y dir ]
      where
      openModule_x env = env{currentScope = sInfo{scopeModules = mods'}}
        where sInfo = currentScope env
              amod  = scopeCurrent sInfo
              mods  = scopeModules sInfo
              news  = setScopeAccess PrivateNS 
                    $ applyImportDirective dir
                    $ maybe __IMPOSSIBLE__  restrictPrivate
                    $ Map.lookup x mods
              mods' = Map.update (Just . (`mergeScope` news)) amod mods


-- Declaration instances --------------------------------------------------

instance ToConcrete [A.Declaration] [C.Declaration] where
    toConcrete ds = concat <$> mapM toConcrete ds

instance ToConcrete A.RHS (C.RHS, [C.Expr], [C.Expr], [C.Declaration]) where
    toConcrete (A.RHS e) = do
      e <- toConcrete e
      return (C.RHS e, [], [], [])
    toConcrete A.AbsurdRHS = return (C.AbsurdRHS, [], [], [])
    toConcrete (A.WithRHS _ es cs) = do
      es <- toConcrete es
      cs <- toConcrete cs
      return (C.AbsurdRHS, [], es, concat cs)
    toConcrete (A.RewriteRHS _ eqs rhs wh) = do
      wh <- toConcrete wh
      (rhs, eqs', es, whs) <- toConcrete rhs
      unless (null eqs')
        __IMPOSSIBLE__
      eqs <- toConcrete eqs
      return (rhs, eqs, es, wh ++ whs)

data TypeAndDef = TypeAndDef A.TypeSignature A.Definition

instance ToConcrete TypeAndDef [C.Declaration] where
  -- We don't do withInfixDecl here. It's done at the declaration level.

  toConcrete (TypeAndDef (ScopedDecl scope [d]) def) =
    withScope scope $ toConcrete (TypeAndDef d def)

  toConcrete (TypeAndDef d (ScopedDef scope def)) =
    withScope scope $ toConcrete (TypeAndDef d def)

  toConcrete (TypeAndDef (Axiom _ x t) (FunDef i _ cs)) =
    withAbstractPrivate i $ do
    t'  <- toConcreteCtx TopCtx t
    cs' <- toConcrete cs
    x'  <- unsafeQNameToName <$> toConcrete x
    return $ TypeSig x' t' : concat cs'

  toConcrete (TypeAndDef (Axiom _ x t) (DataDef i _ ind bs cs)) =
    withAbstractPrivate i $
    bindToConcrete tel $ \tel' -> do
      t'       <- toConcreteCtx TopCtx t0
      (x',cs') <- (unsafeQNameToName -*- id) <$> toConcrete (x, map Constr cs)
      return [ C.Data (getRange i) ind x' tel' t' cs' ]
    where
      (tel, t0) = mkTel (length bs) t
      mkTel 0 t            = ([], t)
      mkTel n (A.Pi _ b t) = (b++) -*- id $ mkTel (n - 1) t
      mkTel _ _            = __IMPOSSIBLE__

  toConcrete (TypeAndDef (Axiom _ x t) (RecDef  i _ c bs _ cs)) =
    withAbstractPrivate i $
    bindToConcrete tel $ \tel' -> do
      t'       <- toConcreteCtx TopCtx t0
      (x',cs') <- (unsafeQNameToName -*- id) <$> toConcrete (x, map Constr cs)
      c'       <- Trav.mapM (\d -> unsafeQNameToName <$>
                                     toConcrete (axiomName d)) c
      return [ C.Record (getRange i) x' c' tel' t' cs' ]
    where
      (tel, t0) = mkTel (length bs) t
      mkTel n (A.ScopedExpr _ t) = mkTel n t
      mkTel 0 t                  = ([], t)
      mkTel n (A.Pi _ b t)       = (b++) -*- id $ mkTel (n - 1) t
      mkTel _ _                  = __IMPOSSIBLE__

  toConcrete _ = __IMPOSSIBLE__

instance ToConcrete (Constr A.Constructor) C.Declaration where
  toConcrete (Constr (A.ScopedDecl scope [d])) =
    withScope scope $ toConcrete (Constr d)
  toConcrete (Constr (A.Axiom i x t)) = do
    x' <- unsafeQNameToName <$> toConcrete x
    t' <- toConcreteCtx TopCtx t
    return $ C.TypeSig x' t'
  toConcrete (Constr d) = head <$> toConcrete d

instance ToConcrete A.Clause [C.Declaration] where
  toConcrete (A.Clause lhs rhs wh) =
      bindToConcrete lhs $ \(C.LHS p wps _ _) -> do
          (rhs', eqs, with, wcs) <- toConcreteCtx TopCtx rhs
--           ds         <- toConcrete wh
--           let wh' = case ds of
--                 []  -> C.NoWhere
--                 _   -> C.AnyWhere ds
          let wh' = C.NoWhere
          return $ FunClause (C.LHS p wps eqs with) rhs' wh' : wcs

instance ToConcrete A.Declaration [C.Declaration] where
  toConcrete (ScopedDecl scope ds) =
    withScope scope $ toConcrete ds

  toConcrete (Axiom i x t) = do
    x' <- unsafeQNameToName <$> toConcrete x
    withAbstractPrivate i $
      withInfixDecl i x'  $ do
      t' <- toConcreteCtx TopCtx t
      return [C.Postulate (getRange i) [C.TypeSig x' t']]

  toConcrete (A.Field i h x t) = do
    x' <- unsafeQNameToName <$> toConcrete x
    withAbstractPrivate i $
      withInfixDecl i x'  $ do
      t' <- toConcreteCtx TopCtx t
      return [C.Field h x' t']

  toConcrete (A.Primitive i x t) = do
    x' <- unsafeQNameToName <$> toConcrete x
    withAbstractPrivate i $
      withInfixDecl i x'  $ do
      t' <- toConcreteCtx TopCtx t
      return [C.Primitive (getRange i) [C.TypeSig x' t']]

  toConcrete (Definition i ts ds) = do
      ixs' <- map (id -*- unsafeQNameToName) <$> toConcrete (map (DontTouchMe -*- id) ixs)
      withInfixDecls ixs' $ do
        ds' <- concat <$> toConcrete (zipWith TypeAndDef ts ds)
        return [mutual (getRange i) ds']
      where
          ixs = map getInfoAndName ts
          is  = map fst ixs
          getInfoAndName (A.Axiom i x _)          = (i,x)
          getInfoAndName (A.ScopedDecl scope [d]) = getInfoAndName d
          getInfoAndName _                        = __IMPOSSIBLE__

          mutual r [d] = d
          mutual r ds  = C.Mutual r ds

  toConcrete (A.Section i x tel ds) = do
    x <- toConcrete x
    bindToConcrete tel $ \tel -> do
    ds <- toConcrete ds
    return [ C.Module (getRange i) x tel ds ]

  toConcrete (A.Apply i x tel y es _ _) = do
    x  <- unsafeQNameToName <$> toConcrete x
    y  <- toConcrete y
    bindToConcrete tel $ \tel -> do
    es <- toConcrete es
    let r = fuseRange y es
    return [ C.ModuleMacro (getRange i) x tel
                (foldl (C.App r) (C.Ident y) es) DontOpen
                (ImportDirective r (Hiding []) [] False)
           ]

  toConcrete (A.Import i x) = do
    x <- toConcrete x
    return [ C.Import (getRange i) x Nothing DontOpen defaultImportDir ]

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
        A.EtaPragma x -> C.EtaPragma r <$> toConcrete x

-- Left hand sides --------------------------------------------------------

noImplicitArgs = filter (noImplicit . namedThing . unArg)
noImplicitPats = filter noImplicit

noImplicit (A.ImplicitP _) = False
noImplicit _               = True

instance ToConcrete A.LHS C.LHS where
    bindToConcrete (A.LHS i x args wps) ret = do
      bindToConcreteCtx TopCtx (A.DefP info x args) $ \lhs ->
        bindToConcreteCtx TopCtx (noImplicitPats wps) $ \wps ->
          ret $ C.LHS lhs wps [] []
      where info = PatRange (getRange i)

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

-- Helpers for recovering C.OpApp ------------------------------------------

data Hd = HdVar A.Name | HdCon A.QName | HdDef A.QName

tryToRecoverOpApp :: A.Expr -> AbsToCon C.Expr -> AbsToCon C.Expr
tryToRecoverOpApp e def = recoverOpApp bracket C.OpApp view e def
  where
    view e = case AV.appView e of
      NonApplication _   -> Nothing
      Application h args -> Just (mkHd h, args)

    mkHd (HeadVar x)     = HdVar x
    mkHd (HeadCon (c:_)) = HdCon c
    mkHd (HeadCon [])    = __IMPOSSIBLE__
    mkHd (HeadDef f)     = HdDef f

tryToRecoverOpAppP :: A.Pattern -> AbsToCon C.Pattern -> AbsToCon C.Pattern
tryToRecoverOpAppP p def = recoverOpApp bracketP_ C.OpAppP view p def
  where
    view p = case p of
      ConP _ (AmbQ (c:_)) ps -> Just (HdCon c, ps)
      DefP _ f            ps -> Just (HdDef f, ps)
      _                      -> Nothing

recoverOpApp :: (ToConcrete a c, HasRange c) =>
                ((Precedence -> Bool) -> AbsToCon c -> AbsToCon c) ->
                (Range -> C.Name -> [c] -> c) -> (a -> Maybe (Hd, [NamedArg a])) -> a ->
                AbsToCon c -> AbsToCon c
recoverOpApp bracket opApp view e mdefault = case view e of
  Nothing -> mdefault
  Just (hd, args)
    | all notHidden args  -> do
      let  args' = map (namedThing . unArg) args
      case hd of
        HdVar n | isNoName n -> mdefault
                | otherwise  -> do
          x <- toConcrete n
          doCName (nameFixity n) x args'
        HdDef qn -> doQName qn args'
        HdCon qn -> doQName qn args'
    | otherwise -> mdefault
  where

  isNoName x = C.isNoName $ A.nameConcrete x

  notHidden (Arg h _) = h == NotHidden

  -- qualified names can't use mixfix syntax
  doQName qn as = do
    x <- toConcrete qn
    case x of
      C.QName x -> doCName (nameFixity $ qnameName qn) x as
      _         -> mdefault

  -- fall-back (wrong number of arguments or no holes)
  doCName _ cn@(C.Name _ xs) es
    | length xs == 1        = mdefault
    | length es /= numHoles = mdefault
    | List.null es          = mdefault
    where numHoles = length [ () | Hole <- xs ]
          msg = "doCName " ++ showList xs "" ++ " on " ++ show (length es) ++ " args"

  -- binary case
  doCName fixity cn@(C.Name _ xs) as
    | Hole <- head xs
    , Hole <- last xs = do
        let a1     = head as
            an     = last as
            as'    = case as of
                       as@(_:_:_) -> init $ tail as
                       _          -> __IMPOSSIBLE__
        e1 <- toConcreteCtx (LeftOperandCtx fixity) a1
        es <- mapM (toConcreteCtx InsideOperandCtx) as'
        en <- toConcreteCtx (RightOperandCtx fixity) an
        bracket (opBrackets fixity)
            $ return $ opApp (getRange (e1,en)) cn ([e1] ++ es ++ [en])

  -- prefix
  doCName fixity cn@(C.Name _ xs) as
    | Hole <- last xs = do
        let an  = last as
            as' = case as of
                    as@(_:_) -> init as
                    _        -> __IMPOSSIBLE__
        es <- mapM (toConcreteCtx InsideOperandCtx) as'
        en <- toConcreteCtx (RightOperandCtx fixity) an
        bracket (opBrackets fixity)
            $ return $ opApp (getRange (cn,en)) cn (es ++ [en])

  -- postfix
  doCName fixity cn@(C.Name _ xs) as
    | Hole <- head xs = do
        let a1     = head as
            as'    = tail as
        e1 <- toConcreteCtx (LeftOperandCtx fixity) a1
        es <- mapM (toConcreteCtx InsideOperandCtx) as'
        bracket (opBrackets fixity)
            $ return $ opApp (getRange (e1,cn)) cn ([e1] ++ es)

  -- roundfix
  doCName _ cn as = do
    es <- mapM (toConcreteCtx InsideOperandCtx) as
    bracket roundFixBrackets
      $ return $ opApp (getRange cn) cn es

