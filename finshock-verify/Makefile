COQPROJECT := _CoqProject
COQMAKEFILE := CoqMakefile

.PHONY: build clean

build:
	rocq makefile -f $(COQPROJECT) -o $(COQMAKEFILE)
	$(MAKE) -f $(COQMAKEFILE)

clean:
	@if [ -f "$(COQMAKEFILE)" ]; then $(MAKE) -f $(COQMAKEFILE) clean; fi
	@rm -f $(COQMAKEFILE) $(COQMAKEFILE).conf
