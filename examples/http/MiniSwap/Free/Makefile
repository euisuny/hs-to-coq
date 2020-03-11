all:
	$(MAKE) -C .. free
	# $(MAKE) examples

coq: Makefile.coq
	$(MAKE) -f $<

examples: Examples/Makefile.coq
	$(MAKE) -C Examples -f Makefile.coq

install: Makefile.coq all
	$(MAKE) -f $< install

Makefile.coq: _CoqProject
	coq_makefile -f $< -o $@

Examples/Makefile.coq: Examples/_CoqProject
	cd Examples; coq_makefile -f _CoqProject -o Makefile.coq

clean: Makefile.coq
	$(MAKE) -f $< clean
	$(RM) $<*
	$(RM) */.*.aux

.PHONY: all build run clean examples
