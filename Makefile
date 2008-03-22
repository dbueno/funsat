all: dpllsat

dpllsat:
	runghc Setup.lhs build

TAGS: DPLLSat.hs Main.hs
	hasktags DPLLSat.hs Main.hs

# Dump generated code to stdout, so one can grep for function names of type
# class instances, e.g. $f8.
.PHONY: dump
dump:
	ghc --make $(GHC_OPTS) -fforce-recomp -fno-code -ddump-simpl -main-is DPLLSat DPLLSat.hs

clean:
	rm -f *.o *.hi *.prof
	rm -f $(BIN) sat-micro