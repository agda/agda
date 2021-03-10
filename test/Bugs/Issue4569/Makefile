# Makefile for mock project for issue #4569

default:
	cabal v1-install -O0 --enable-shared --enable-executable-dynamic --disable-static

clean:
	ghc-pkg unregister HelloWorld
	rm ~/.cabal/bin/hello-world
	rm ~/.cabal/lib/x86_64-osx-ghc-8.4.4/libHSHelloWorld*

debug:
	otool -l dist/build/hello-world/hello-world | less
#	otool -tvV dist/build/hello-world/hello-world | less

# EOF
