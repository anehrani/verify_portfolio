COQPROJECT := _CoqProject
COQMAKEFILE := CoqMakefile

.PHONY: all build audit clean

all: build

build:
	rocq makefile -f $(COQPROJECT) -o $(COQMAKEFILE)
	$(MAKE) -f $(COQMAKEFILE)

audit: build
	rocq check -silent \
		-R finshock-verify/theories FinShockVerify \
		-R formal-mathfin-coq/theories MathFin \
		-Q option-matching-paper Top \
		-Q src FinanceVerify.Legacy \
		-Q theories FinanceVerify \
		-o FinanceVerify.Audit

clean:
	@if [ -f "$(COQMAKEFILE)" ]; then $(MAKE) -f $(COQMAKEFILE) clean; fi
	@rm -f $(COQMAKEFILE) $(COQMAKEFILE).conf
