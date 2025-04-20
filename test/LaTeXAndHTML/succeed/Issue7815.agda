module Issue7815 where
module X where
module _
  (a : Set) -- Before fixing issue 7815, `a` and `Set` were not highlighted.
  (let module Y = X)
  where
