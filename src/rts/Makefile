
.PHONY : default

.setup-config : agda-rts.cabal Setup.hs RTP.hs RTN.hs RTS.hs
	runhaskell Setup.hs configure

default : .setup-config
	runhaskell Setup.hs build
	runhaskell Setup.hs register --user --inplace

