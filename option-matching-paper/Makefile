COQPROJECT := _CoqProject
COQMAKEFILE := CoqMakefile

.PHONY: build audit clean

build:
	rocq makefile -f $(COQPROJECT) -o $(COQMAKEFILE)
	$(MAKE) -f $(COQMAKEFILE)

audit: build
	rocq check -silent -Q . Top -o Top.Audit

clean:
	@if [ -f "$(COQMAKEFILE)" ]; then $(MAKE) -f $(COQMAKEFILE) clean; fi
	@rm -f $(COQMAKEFILE) $(COQMAKEFILE).conf
