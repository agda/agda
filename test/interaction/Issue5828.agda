
data X : Set
  where x : X

pattern y = x

theorem : X
theorem = {!-r!}
