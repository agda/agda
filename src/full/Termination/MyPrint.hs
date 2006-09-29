
class MyPrint a where
  myprint :: a -> String

myprintArgs :: Args -> String
myprintArgs args = sepBy " " (map myprint args)

instance MyPrint Term where
  myprint (Var id args) = "x" ++ show id ++ myprintArgs args
  myprint _ = "?"

instance MyPrint a => MyPrint (Arg a) where
  myprint =  myprint . unArg

instance MyPrint Pattern where
