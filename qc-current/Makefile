-include CONFIGURE
COQMFFLAGS := -Q . QC 

ALLVFILES := Preface.v Introduction.v Typeclasses.v QC.v TImp.v QuickChickTool.v QuickChickInterface.v Postscript.v Bib.v 

build: Makefile.coq
	$(MAKE) -f Makefile.coq

clean:
	if [ -e Makefile.coq ]; then $(MAKE) -f Makefile.coq cleanall; fi
	$(RM) $(wildcard Makefile.coq Makefile.coq.conf) 

Makefile.coq:
	coq_makefile $(COQMFFLAGS) -o Makefile.coq $(ALLVFILES)

.PHONY: build clean
