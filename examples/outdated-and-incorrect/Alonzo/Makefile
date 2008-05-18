ALONZO=agda -c
TESTS=Q Printf Proj TestWith
RTMODS = RTS RTP
PRELUDEMODS=AlonzoPrelude PreludeBool PreludeNat PreludeList PreludeString \
  PreludeShow PreludeInt PreludeAll

tests: prelude #$(TESTS)
	for i in $(TESTS) ; do \
	  #$(ALONZO) $$i.agda; ghc -c $$i.hs ; \
	  ./almake $$i ; \
	done

Q: Q.agda
	$(ALONZO) Q.agda
	ghc -c Q.hs


runtime:
	ghc -c RTS.hs
	ghc -c RTN.hs
	ghc -c RTP.hs


prelude: runtime
	for i in $(PRELUDEMODS); do \
          echo "Compiling $$i"; $(ALONZO) $$i.agda; ghc -c $$i.hs ; \
	done


clean:
	for i in $(PRELUDEMODS); do \
	  rm -f $$i.hs ; \
	done
	-rm -f $(TESTS)
	-rm -f *.hi *.o *~ *.agdai