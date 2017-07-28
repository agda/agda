-- Andreas, 2017-07-28, issue 1077

open import Issue1077

foz = foo
baz = bar

-- WAS: bar not in scope

-- NOW: import fails because module Issue1077 is rejected
