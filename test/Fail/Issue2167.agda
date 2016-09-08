-- Andreas, 2016-09-08, issue #2167 reported by effectfully

loop : Set₁
loop = .Set

-- WAS: looping of type checker
-- NOW: proper error about invalid dotted expression
