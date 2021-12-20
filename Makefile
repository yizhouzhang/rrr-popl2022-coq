CPDT := lib/cpdt

all: rrr

rrr: cpdt Makefile.coq

Makefile.coq: _CoqProject
ifeq ($(wildcard Makefile.coq),)
	coq_makefile -f _CoqProject -o Makefile.coq
else
endif

include Makefile.coq

cpdt:
	$(MAKE) -C $(CPDT)

clean::
	rm -f Makefile.coq Makefile.coq.bak

cleanall::
	$(MAKE) -C $(CPDT) clean

.PHONY: rrr cpdt
