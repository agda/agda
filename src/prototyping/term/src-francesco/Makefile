
bnfc_output = $(patsubst %,../dist/Syntax/%,Abs.hs ErrM.hs Layout.hs Print.hs Lex.x Par.y)
gen_hs_files = $(patsubst %,../dist/Syntax/%.hs,Par Lex Abs ErrM Layout Print)

$(bnfc_output) : Syntax.cf
	-@mkdir -p ../dist
	-@rm $(bnfc_output)
	@(cd ../dist && bnfc -d ../src/$<)

../dist/%.hs : ../dist/%.y
	happy -o $@ $< -i

../dist/%.hs : ../dist/%.x
	alex -o $@ $<

./dist/build/tc/tc : $(gen_hs_files)
	cabal build

