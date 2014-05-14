{-# LANGUAGE RankNTypes #-}

module Check where

import           Data.Functor                     ((<$>))
import           Data.Void                        (Void)

import           Syntax.Abstract                  (Name)
import qualified Syntax.Abstract                  as A
import qualified Impl                             as I
import           Term
import           Term.View

whnfView :: I.Term v -> I.TC v (I.TermView v)
whnfView = undefined

-- type WithParsHandler = forall v.
--     I.Type v ->
--     -- The leftover from the 'I.Type' arg after the 'Names' have been
--     -- abstracted
--     [I.Term v] ->
--     -- The vars corresponding to the abstracted names.
--     I.TC v (I.Type v)

-- withPars :: I.ClosedType -> [Name] -> WithParsHandler
--          -> I.TC Void (I.ClosedTelescope I.Type)
-- withPars = go []
--   where
--     go :: [v] -> I.Type v -> [Name] -> WithParsHandler
--        -> I.TC v (I.Telescope I.Type Name)
--     go vars type_ []       ret = I.telescopeEmpty <$> ret type_ (map return vars)
--     go vars type_ (n : ns) ret =
--         I.telescopeExtend undefined n <$> go 

-- checkData
--     :: Name
--     -- ^ Name of the tycon
--     -> [Name]
--     -- ^ Name of the parameters to the tycons
--     -> [A.TypeSig]
--     -- ^ Data constructors
--     -> TC Void ()
-- checkData tyCon tyConPars absDataCons = do
--     tyConType <- getDefinition tyCon
--     addConstant tyCon Data tyConType
--     withPars tyConType tyConPars $ \tyConPars' tyConTypeEnd -> do
--         set <- I.unview Set
--         equalType tyConTypeEnd set
--         dataConTypeEnd <- unview $ App (Def tyCon) (map apply tyConPars')
--         mapM_ (checkDataCon tyCon dataConTypeEnd) absDataCons

-- checkDataCon
--     :: Name
--     -- ^ Name of the type constructor
--     -> Type v
--     -- ^ The type that should be found as return type of each data
--     -- constructor.
--     -> A.TypeSig
--     -- ^ The type of the data constructor
-- checkDataCon tyCon dataConTypeEnd (A.Sig dataCon absDataConType) =
--     atSrcLoc dataCon $ do
--         dataConType <- isType absDataConType
--         dataConTypeEnd <- discharge


-- Main functions
------------------------------------------------------------------------

check :: A.Expr -> I.Type v -> I.TC v (I.Term v)
check = undefined

infer :: A.Expr -> I.TC v (I.Term v, I.Type v)
infer = undefined

inferHead :: A.Head -> I.TC v (Head v, I.Type v)
inferHead = undefined

checkEqual :: I.Type v -> I.Term v -> I.Term v -> I.TC v ()
checkEqual ty x y = undefined

-- Utils
------------------------------------------------------------------------

equalType :: I.Type v -> I.Type v -> I.TC v ()
equalType a b = do
  let set = I.unview Set
  checkEqual set a b

isType :: A.Expr -> I.TC v (I.Type v)
isType abs = do
    let set = I.unview Set
    check abs set

-- check :: A.Expr -> I.Type v -> I.TC v (I.Term v)
-- check syn type_ = atSrcLoc syn $ case syn of
--   A.App (A.Con con) args -> do
--     def <- I.definitionOf con
--     case def of
--       Constructor _ dataName tele -> do
--         typeView <- whnfView type_
--         case typeView of
--           App (Def dataName') argsTypes0
--             | dataName == dataName', Just argTypes <- mapM isApply els -> do
--               type_ <- substs tele argTypes
--               h <- unview (App (Con c) [])
--               r <- checkSpine h es b
--               case r of
--                 NotStuck (v, _) -> return v
--                 Stuck pid       -> do
--                   x <- freshMeta a
--                   subProblem pid $ \(v, _) -> equal a x v
--                   return x
--           _ -> conError
--       _ -> conError
--   where
--     conError = typeError $ "Constructor type error " ++ show e ++ " : " ++ show a
--   -- A.App (A.Refl l) es -> do
--   --   when (not $ null es) $
--   --     typeError $ "Type error: refl applied to arguments: refl " ++ show es
--   --   av <- whnfView a
--   --   case av of
--   --     NotBlocked (Equal b x y) -> do
--   --       r    <- equal b x y
--   --       refl <- unview (App Refl [])
--   --       case r of
--   --         NotStuck _ -> return refl
--   --         Stuck pid  -> do
--   --           z <- freshMeta a
--   --           subProblem pid $ \_ -> equal a z refl
--   --           return z
--   --     _ -> typeError $ show (ignoreBlocking av) ++
--   --                      " is (perhaps) not an application of the equality type"
--   -- A.Meta l -> freshMeta a
--   -- A.Lam x body -> do
--   --   av <- whnfView a
--   --   case av of
--   --     NotBlocked (Pi a (Abs _ b)) -> do
--   --       body <- extendContext x a $ \_ -> check body b
--   --       unview (Lam (Abs (A.nameString x) body))
--   --     NotBlocked (App (Meta i) us) ->
--   --       typeError $ "todo check\n  " ++ show e ++ " : " ++ show a
--   --     Blocked x a -> do
--   --       typeError $ "todo check\n  " ++ show e ++ " : (blocked) " ++ show a
--   --     a -> typeError $ "Lambda type error " ++ show e ++ " : " ++ show a
--   -- _ -> do
--   --   r <- infer e
--   --   case r of
--   --     NotStuck (v, b) -> do
--   --       r <- equalType a b
--   --       case r of
--   --         NotStuck () -> return v
--   --         Stuck pid   -> do
--   --           x <- freshMeta a
--   --           subProblem pid $ \_ -> equal a x v
--   --           return x
--   --     Stuck pid -> do
--   --       x <- freshMeta a
--   --       subProblem pid $ \(v, b) -> do
--   --         equalType a b `bindStuck` \_ -> equal a x v
--   --       return x
