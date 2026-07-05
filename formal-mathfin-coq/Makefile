COQPROJECT := _CoqProject
COQMAKEFILE := CoqMakefile

.PHONY: build audit clean

build:
	rocq makefile -f $(COQPROJECT) -o $(COQMAKEFILE)
	$(MAKE) -f $(COQMAKEFILE)

audit: build
	rocq check -silent -R theories MathFin -o MathFin.AxiomAudit

clean:
	@if [ -f "$(COQMAKEFILE)" ]; then $(MAKE) -f $(COQMAKEFILE) clean; fi
	@rm -f $(COQMAKEFILE) $(COQMAKEFILE).conf
