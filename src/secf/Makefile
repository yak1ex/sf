COQMFFLAGS := -Q . SECF  

ALLVFILES := Maps.v Imp.v Equiv.v Hoare.v Hoare2.v Preface.v Noninterference.v StaticIFC.v SpecCT.v Postscript.v Bib.v  MapsTest.v  ImpTest.v  EquivTest.v  HoareTest.v  Hoare2Test.v  PrefaceTest.v  NoninterferenceTest.v  StaticIFCTest.v  SpecCTTest.v  PostscriptTest.v  BibTest.v

build: Makefile.coq
	$(MAKE) -f Makefile.coq

clean::
	if [ -e Makefile.coq ]; then $(MAKE) -f Makefile.coq cleanall; fi
	$(RM) $(wildcard Makefile.coq Makefile.coq.conf) 

Makefile.coq:
	rocq makefile $(COQMFFLAGS) -o Makefile.coq $(ALLVFILES)

-include Makefile.coq

.PHONY: build clean
