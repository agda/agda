-- Andreas, 2024-08-24, error wrong quantity for constructor

data LinD : Set where
  @1 c : LinD

-- should fail, e.g. parse error
-- or trigger warning FixingQuantity
