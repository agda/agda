
## Rules for using Cabal ##################################################

ifeq ($(HAVE_RUNHASKELL),Yes)

SETUP	   = Setup.hs
RUNSETUP   = $(RUNHASKELL) $(SETUP)

else

SETUP	   = setup
RUNSETUP   = ./setup

$(SETUP) : Setup.hs
	ghc --make -o $@ $<

endif

