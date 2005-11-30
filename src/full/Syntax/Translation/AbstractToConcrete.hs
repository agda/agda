{-# OPTIONS -cpp -fglasgow-exts -fallow-overlapping-instances -fallow-undecidable-instances #-}

{-| The translation of abstract syntax to concrete syntax has two purposes.
    First it allows us to pretty print abstract syntax values without having to
    write a dedicated pretty printer, and second it serves as a sanity check
    for the concrete to abstract translation: translating from concrete to
    abstract and then back again should be (more or less) the identity.
-}
module Syntax.Translation.AbstractToConcrete where

import Control.Monad.Reader

import Syntax.Common
import Syntax.Position
import Syntax.Info
import Syntax.Concrete as C
import Syntax.Abstract as A

import Utils.Maybe
import Utils.Monad
import Utils.Tuple

#include "../../undefined.h"

-- Flags ------------------------------------------------------------------

-- | The translation is configurable. Currently you can choose whether to
--   make use of the pieces of concrete syntax stored in the info parts of
--   the abstract syntax. When pretty printing, this is what you want, but
--   if the purpose is to verify the correctness of the translation from
--   concrete to abstract we want to look at all of the abstract syntax.
data Flags = Flags  { useStoredConcreteSyntax :: Bool
		    , precedenceLevel	      :: Precedence
		    }

defaultFlags :: Flags
defaultFlags = Flags { useStoredConcreteSyntax	= True
		     , precedenceLevel		= TopCtx
		     }

-- The Monad --------------------------------------------------------------

-- | We make the translation monadic for modularity purposes.
type AbsToCon = Reader Flags

abstractToConcrete :: ToConcrete a c => Flags -> a -> c
abstractToConcrete flags a = runReader (toConcrete a) flags

-- Dealing with stored syntax ---------------------------------------------

-- | Indicates that the argument is a stored piece of syntax which
--   should only be used 
stored :: a -> AbsToCon (Maybe a)
stored x =
    do	b <- useStoredConcreteSyntax <$> ask
	return $ if b then Just x else Nothing

withStored :: ToConcrete i (Maybe c) => i -> AbsToCon c -> AbsToCon c
withStored i m = fromMaybeM m (toConcrete i)

-- Dealing with precedences -----------------------------------------------

-- | General bracketing function.
bracket' ::    (e -> e)		    -- ^ the bracketing function
	    -> (Precedence -> Bool) -- ^ do we need brackets
	    -> e -> AbsToCon e
bracket' paren needParen e =
    do	p <- precedenceLevel <$> ask
	return $ if needParen p then paren e else e

-- | Expression bracketing
bracket :: (Precedence -> Bool) -> AbsToCon C.Expr -> AbsToCon C.Expr
bracket par m =
    do	e <- m
	bracket' (Paren (getRange e)) par e

-- | Pattern bracketing
bracketP :: (Precedence -> Bool) -> AbsToCon C.Pattern -> AbsToCon C.Pattern
bracketP par m =
    do	e <- m
	bracket' (ParenP (getRange e)) par e

-- Dealing with infix declarations ----------------------------------------

-- | If a name is defined with a fixity that differs from the default, we have
--   to generate a fixity declaration for that name.
infixDecl :: DefInfo -> Name -> [C.Declaration]
infixDecl i x
    | defFixity i == defaultFixity  = []
    | otherwise			    = [C.Infix (defFixity i) [x]]

-- Dealing with private definitions ---------------------------------------

mkPrivate :: DefInfo -> AbsToCon [C.Declaration] -> AbsToCon [C.Declaration]
mkPrivate i m =
    case defAccess i of
	PublicAccess	-> m
	PrivateAccess	->
	    do	ds <- m
		return [ C.Private (getRange ds) ds ]

-- The To Concrete Class --------------------------------------------------

class ToConcrete a c | a -> c where
    toConcrete :: a -> AbsToCon c

-- | Translate something in a context of the given precedence.
toConcreteCtx :: ToConcrete a c => Precedence -> a -> AbsToCon c
toConcreteCtx p x = local (\f -> f { precedenceLevel = p }) $ toConcrete x

-- Info instances ---------------------------------------------------------

instance ToConcrete ExprInfo (Maybe C.Expr) where
    toConcrete (ExprSource _ f)	=
	do  p <- precedenceLevel <$> ask
	    stored (f p)
    toConcrete _		= return Nothing

instance ToConcrete DeclInfo (Maybe [C.Declaration]) where
    toConcrete (DeclSource ds)	= stored ds
    toConcrete _		= return Nothing

instance ToConcrete DefInfo (Maybe [C.Declaration]) where
    toConcrete info = toConcrete $ defInfo info

instance ToConcrete LHSInfo (Maybe C.LHS) where
    toConcrete (LHSSource lhs) = stored lhs

instance ToConcrete PatInfo (Maybe C.Pattern) where
    toConcrete (PatSource _ f) =
	do  p <- precedenceLevel <$> ask
	    stored (f p)
    toConcrete (PatRange _) = return Nothing

newtype Force a = Force a

instance ToConcrete i (Maybe c) => ToConcrete (Force i) c where
    toConcrete (Force i) =
	do  Just c <- local (\s -> s { useStoredConcreteSyntax = True })
			$ toConcrete i
	    return c

-- General instances ------------------------------------------------------

instance ToConcrete a c => ToConcrete [a] [c] where
    toConcrete = mapM toConcrete

-- Expression instance ----------------------------------------------------

instance ToConcrete A.Expr C.Expr where
    toConcrete (Var i _) = return $ Ident (concreteName i)
    toConcrete (Def i _) = return $ Ident (concreteName i)
    toConcrete (Con i _) = return $ Ident (concreteName i)
	-- for names we have to use the name from the info, since the abstract
	-- name has been resolved to a fully qualified name (except for
	-- variables)
    toConcrete (A.Lit l)	    = return $ C.Lit l
    toConcrete (A.QuestionMark i)   = return $ C.QuestionMark (getRange i)
    toConcrete (A.Underscore i)	    = return $ C.Underscore (getRange i)

    -- We don't have to do anything to recognise infix applications since
    -- they have been stored away (and if we're not using the stored
    -- information we don't care).
    toConcrete (A.App i h e1 e2)    =
	withStored i
	$ bracket appBrackets
	$ do e1' <- toConcreteCtx FunctionCtx e1
	     e2' <- toConcreteCtx (hiddenArgumentCtx h) e2
	     return $ C.App (getRange i) h e1' e2'

    -- Similar to the application case we don't try to recover lambda sugar
    -- (i.e. @\\x -> \\y -> e@ to @\\x y -> e@).
    toConcrete (A.Lam i b e)	    =
	withStored i
	$ bracket lamBrackets
	$ do b' <- toConcrete b
	     e' <- toConcreteCtx TopCtx e
	     return $ C.Lam (getRange i) [b'] e'

    -- Same thing goes for pis. We don't care if it was a 'Fun' or a 'Pi'.
    toConcrete (A.Pi i b e)	    =
	withStored i
	$ bracket piBrackets
	$ do b' <- toConcrete b
	     e' <- toConcreteCtx TopCtx e
	     return $ C.Pi b' e'

    toConcrete (A.Set i n)  = withStored i $ return $ C.SetN (getRange i) n
    toConcrete (A.Prop i)   = withStored i $ return $ C.Prop (getRange i)

    toConcrete (A.Let i ds e) =
	withStored i
	$ bracket lamBrackets
	$ do ds' <- toConcrete ds
	     e'  <- toConcreteCtx TopCtx e
	     return $ C.Let (getRange i) ds' e'

-- Binder instances -------------------------------------------------------

instance ToConcrete A.LamBinding C.LamBinding where
    toConcrete (A.DomainFree h x) = return $ C.DomainFree h x
    toConcrete (A.DomainFull b)   = C.DomainFull <$> toConcrete b

instance ToConcrete A.TypedBinding C.TypedBinding where
    toConcrete (A.TypedBinding r h xs e) =
	C.TypedBinding r h xs <$> toConcreteCtx TopCtx e

-- Declaration instances --------------------------------------------------

instance ToConcrete [A.Declaration] [C.Declaration] where
    toConcrete ds = concat <$> mapM toConcrete ds

instance ToConcrete (A.TypeSignature, A.Definition) [C.Declaration] where

    toConcrete (Axiom _ x t, FunDef i _ cs) =
	mkPrivate i $
	do  t'  <- toConcreteCtx TopCtx t
	    cs' <- withStored i $ toConcrete cs
	    return $ infixDecl i x ++ TypeSig x t' : cs'

    toConcrete (Axiom _ x t, DataDef i _ bs cs) =
	mkPrivate  i $	-- mkPrivate has to be applied outside the withStored
	withStored i $
	do  tel' <- toConcrete tel
	    t'   <- toConcreteCtx TopCtx t0
	    cs'  <- toConcrete $ map Constr cs
	    return $ infixDecl i x ++ [ C.Data (getRange i) x tel' t' cs' ]
	where
	    (tel, t0) = mkTel (length bs) t
	    mkTel 0 t		    = ([], t)
	    mkTel n (A.Pi _ b t)    = (b:) -*- id $ mkTel (n - 1) t
	    mkTel _ _		    = __IMPOSSIBLE__

    toConcrete _ = __IMPOSSIBLE__

newtype Constr a = Constr a

instance ToConcrete (Constr A.Constructor) C.Declaration where
    toConcrete (Constr (A.Axiom i x t)) =
	C.TypeSig x <$> toConcreteCtx TopCtx t
    toConcrete _ = __IMPOSSIBLE__

instance ToConcrete A.Clause C.Declaration where
    toConcrete (A.Clause lhs rhs wh) =
	do  lhs' <- toConcrete lhs
	    rhs' <- toConcreteCtx TopCtx rhs
	    wh'  <- toConcrete wh
	    return $ FunClause lhs' rhs' wh'

instance ToConcrete A.Declaration [C.Declaration] where

    toConcrete (Axiom i x t) =
	mkPrivate  i $
	withStored i $
	do  t' <- toConcreteCtx TopCtx t
	    return $ infixDecl i x ++
		     [C.Postulate (getRange i) [C.TypeSig x t']]

    toConcrete (Synonym i x e wh) =
	mkPrivate  i $
	withStored i $
	do  e'  <- toConcreteCtx TopCtx e
	    wh' <- toConcrete wh
	    return $ infixDecl i x ++
		     [C.FunClause (C.LHS (getRange x) PrefixDef x []) e' wh']

    toConcrete (Definition i ts ds) =
	withStored i $
	do  ds' <- concat <$> toConcrete (zip ts ds)
	    return [C.Mutual (getRange i) ds']

    toConcrete (A.Abstract i ds) =
	withStored i $
	do  ds' <- toConcrete ds
	    return [C.Abstract (getRange i) ds']

    toConcrete (A.Module i x tel ds) =
	withStored i $
	do  tel' <- toConcrete tel
	    ds'  <- toConcrete ds
	    return [C.Module (getRange i) x tel' ds']

    -- There is no way we could restore module defs, imports and opens
    -- without having the concrete version stored away.
    toConcrete (A.ModuleDef (DefInfo _ _ (DeclSource ds)) _ _ _ _)
					= return ds
    toConcrete (A.ModuleDef _ _ _ _ _)	= __IMPOSSIBLE__

    toConcrete (A.Import (DeclSource ds) _) = return ds
    toConcrete (A.Import _ _) = __IMPOSSIBLE__

    toConcrete (A.Open (DeclSource ds))	= return ds
    toConcrete (A.Open _) = __IMPOSSIBLE__

-- Left hand sides --------------------------------------------------------

instance ToConcrete a c => ToConcrete (Arg a) (Arg c) where
    toConcrete (Arg h x) =
	Arg h <$> toConcreteCtx (hiddenArgumentCtx h) x

instance ToConcrete A.LHS C.LHS where
    toConcrete (A.LHS i x args) =
	withStored i $
	do  args' <- toConcrete args
	    return $ C.LHS (getRange i) PrefixDef x args'

instance ToConcrete A.Pattern C.Pattern where
    toConcrete (VarP x)		= return $ IdentP (QName x)
    toConcrete (A.WildP i)	=
	withStored i $ return $ C.WildP (getRange i)
    toConcrete (ConP i x args)  = toConcrete (Force i)

--  We can't figure out the original name without looking at the stored
--  pattern.
-- 	withStored i $
-- 	do  args' <- toConcrete args
-- 	    return $ foldl appP (IdentP x) args'
-- 	where
-- 	    appP p (Arg h q) = AppP h p q
	

