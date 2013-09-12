
bnfc_output = $(patsubst %,../dist/Syntax/%,Abs.hs ErrM.hs Layout.hs Print.hs Lex.x Par.y)
gen_hs_files = $(patsubst %,../dist/Syntax/%.hs,Par Lex Abs ErrM Layout Print)

ghc_flags = -fwarn-incomplete-patterns -Werror

default : ../dist/tc

$(bnfc_output) : Syntax.cf
	-@rm $(bnfc_output)
	@(cd ../dist; bnfc -d ../src/$<)

../dist/%.hs : ../dist/%.y
	happy -o $@ $< -i

../dist/%.hs : ../dist/%.x
	alex -o $@ $<

../dist/tc : Main.hs $(gen_hs_files) $(src_files)
	ghc --make -o $@ $< $(ghc_flags) -i../dist -hidir=../dist -odir=../dist

