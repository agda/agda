
variable {A} : Set _

id : A → A
id a = a

test : Set₁
test = id {A = Set₁} Set
