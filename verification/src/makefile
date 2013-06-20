COQC=$(COQBIN)coqc $(COQFLAGS)
COQ=$(COQBIN)coqtop $(COQFLAGS) -batch
COQDEP=$(COQBIN)coqdep -c
COQMK=$(COQBIN)coq_makefile

OPT=-opt
COQFLAGS=-q $(OPT) $(COQINCLUDES)
COQINCLUDES=-I .

ALLV=$(shell ls *.v)
ALLVO=$(ALLV:.v=.vo)

all : $(ALLVO)

.SUFFIXES: .v .vo

.v.vo:
	$(COQC) $<

clean:
	rm -f *~ *.vo *.glob .depend

depend:
	rm -f .depend
	$(COQDEP) -c $(COQINCLUDES) *.v > .depend

-include .depend
