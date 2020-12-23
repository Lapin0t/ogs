ITREEDIR=./lib/InteractionTrees

all: Makefile.coq itree
	@+$(MAKE) -f Makefile.coq all

itree:
	@+$(MAKE) -C $(ITREEDIR)

clean: Makefile.coq
	@+$(MAKE) -f Makefile.coq cleanall
	@rm -f Makefile.coq Makefile.coq.conf

Makefile.coq: _CoqProject
	$(COQBIN)coq_makefile -f _CoqProject -o Makefile.coq

force _CoqProject Makefile: ;

%: Makefile.coq force
	@+$(MAKE) -f Makefile.coq $@

.PHONY: all clean force itree
