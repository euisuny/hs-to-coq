all:
	$(MAKE) -C .. custom

build: Makefile.coq
	$(MAKE) -f $<

install: Makefile.coq build
	$(MAKE) -f $< install

Makefile.coq: _CoqProject
	coq_makefile -f $< -o $@

clean: Makefile.coq
	$(MAKE) -f $< clean
	$(RM) $<*
	$(RM) .*.aux

.PHONY: build clean
