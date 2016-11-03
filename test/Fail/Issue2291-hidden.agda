-- Andreas, 2016-11-03, issue #2291 reported by Aerate

test = let {_} = _ in _

-- WAS: Internal error
-- NOW: Could not parse the left-hand side {_}
