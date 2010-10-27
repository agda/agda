-- | A parser combinator 'binop' for parsing a sequence of operators
--   and expressions (built on top of Parse).

module BinParse(Fixity(..), binop,prec) where
import Parse(Parser, (>>-), (||!), into, succeed, failure)

data Fixity = FInfixl Int | FInfixr Int | FInfix Int
    deriving (Eq, Ord)

prec :: Fixity -> Int
prec (FInfixl i) = i
prec (FInfixr i) = i
prec (FInfix i) = i


binop :: (o -> Fixity) -> -- extract operator fixity
         (a -> o -> a -> a) -> -- combine operands
         Parser t o -> -- parse operator
         Parser t a -> -- parse operand
         Parser t a
binop fix bin op atom = (atom >>- (:[])) `into` opsO []
  where opsO os as = op `into` newop os as
                 ||! succeed (end os as)
        opsA os as = atom `into` (\ a -> opsO os (a:as))
        end [] [a] = a
        end (o:os) (a:b:as) = end os (bin b o a : as)
        end _ _ = error "binop parse: bad operand stack"
        newop [] as iop = opsA [iop] as
        newop oos@(sop:os) as@(~(a:b:as')) iop =
            let (iprec,iass) = prec iop
                (sprec,sass) = prec sop
            in  if iprec==sprec && (iass/=sass || iass==FInfix iprec) then
                failure "ambiguous operator combination"
            else if iprec>sprec || iprec==sprec && iass==FInfixr iprec then
                opsA (iop:oos) as
            else
                newop os (bin b sop a : as') iop
        prec o =
            case fix o of
            f@(FInfixl i) -> (i, f)
            f@(FInfixr i) -> (i, f)
            f@(FInfix  i) -> (i, f)
