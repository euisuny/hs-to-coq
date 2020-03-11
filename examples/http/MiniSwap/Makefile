SERVER = Spec/main
EXCLUDE= Proofs Spec/TopLevelSpec.v Spec/Vst Spec/main.v \
		 Lib/VstLib.v html checkers qc-build Spec/Swap_SimpleSpec_Examples.v \
		 ByteType.v URIMap.v StringUtil.v StatePairMonad.v StringSynonym.v \
		 OptionUtil.v OptionE.v OptionAsOT.v MonadNotations.v ListUtil.v \
		 HttpMessageGen.v Fresh.v ConjectureSet.v Common.v Spec/TopLevelProp.v
# Doesn't seem to work: Spec/SingleSwap_SimpleSpec_Examples.v
#   (and anyway would require patching the _CoqProject when testing, I think)
OCAMLBUILDFLAGS=-libs unix,str
MINI_CLIENT = Test/mini_client.native
MIDDLEBOX = Test/middlebox.native
CLIENT = Spec/client
QC = quickChick -color -top DeepWeb -ocamlbuild '$(OCAMLBUILDFLAGS)' \
	 -cmd '$(MAKE) coq-qc --quiet' $(QCFLAGS)
CFLAGS=-DDEBUG -DBUFFER_SIZE=3
V=@

.PHONY: build clean stop test testmini server build-with-deps coq-qc html tags bcp depgraph

build-with-deps:
	$V$(MAKE) -C .. miniswap

build: Makefile.coq
	$V$(MAKE) -f $<

Makefile.coq: _CoqProject
	$Vcoq_makefile -f $< -o $@

_CoqProject: _CoqProject.Minimal _CoqProject.Vst
	cat $^ > _CoqProject

_CoqProject.Vst:
	touch $@

server: $(SERVER) stop
	@exec $< 2>> /tmp/server_error &

middlebox: $(MIDDLEBOX) stop
	@exec $< 2>> /tmp/middlebox_error &

%.native: %.ml
	@rm -f $@
	@ocamlbuild $(OCAMLBUILDFLAGS) $@
	@mv _build/$@ $@
	@ocamlbuild -clean

coq-qc:
	@perl -i -pe 's:^Proofs:# Proofs:' _CoqProject
	@perl -i -pe 's:^Spec/TopLevelSpec:# Spec/TopLevelSpec:' _CoqProject
	@perl -i -p0e 's/^(Separate Extraction)(\s+\S+)*?((\s+test\S+)*)\s*\.$$/\1\3./m' QuickChickTop.v
	coq_makefile -f _CoqProject -o Makefile.coq 2>> /tmp/client_error
	echo "Building..."
	$(MAKE) -C ..
	$(MAKE) -f Makefile.coq QuickChickTop.vo --quiet
	echo "Start testing..."

qc-build/:
	mkdir -p qc-build/

QC_COQOPTS=-Q ../../Custom Custom -Q ../../Free DeepWeb.Free -Q ../ DeepWeb

qc-build/CoqCheckers.native: build-with-deps qc-build/ checkers/CoqCheckers.v
	cp checkers/CoqCheckers.v qc-build/CoqCheckers.v
	cd qc-build/; \
	  coqc $(QC_COQOPTS) CoqCheckers.v; \
	  ocamlbuild CoqCheckers.native

qc-build/ExternalCheckers.native: build-with-deps qc-build/ checkers/ExternalCheckers.v
	cp checkers/ExternalCheckers.v qc-build/ExternalCheckers.v
	cd qc-build/; \
	  coqc $(QC_COQOPTS) ExternalCheckers.v; \
	  ocamlbuild $(OCAMLBUILDFLAGS) ExternalCheckers.native

new-test-impl-model: qc-build/CoqCheckers.native
	$<

new-test-c: qc-build/ExternalCheckers.native server
	$<

test-impl-model: _CoqProject
	$V$(QC) -s ImplModelTest -exclude $(EXCLUDE)

testcoq-examples: _CoqProject
	$V$(QC) -s SwapExamples -N 100 -exclude $(EXCLUDE)

test-c: server _CoqProject
	$V$(RM) /tmp/server_log /tmp/client_log /tmp/server_error /tmp/client_error
	$V$(QC) -s CTest -N 100 -exclude $(EXCLUDE)
	$V$(MAKE) stop

test:
	@echo
	@echo ------------------- Internal tests ----------------------
	$V$(MAKE) test-impl-model
	$V$(MAKE) testcoq-examples
	@echo
	@echo ------------------- External tests ----------------------
	$V$(MAKE) test-c --no-print-directory

testclient: server $(CLIENT)
	$(CLIENT)
	$(MAKE) stop

# This doesn't work
testmini: server $(MINI_CLIENT)
	$(MINI_CLIENT)
	$(MAKE) stop

testmiddlebox: server $(MIDDLEBOX)
	$(MIDDLEBOX)
	$(MAKE) stop

testmiddlebox_with_client: server middlebox $(MINI_CLIENT)
	$(MINI_CLIENT)
	$(MAKE) stop

stop:
	@if [ -n "$$(pgrep main)" ]; then pkill main; fi

clean: stop
	@if [ -e Makefile.coq ]; then $(MAKE) -f Makefile.coq clean; fi
	@$(RM) -r Makefile.coq* $(SERVER) $(MINI_CLIENT) \
		../_qc_IntegrationExperiment2d.tmp _CoqProject html
	find . -name "*.vo" -print -exec rm -rf {} \;
	find . -name "*.glob" -print -exec rm -rf {} \;

.PHONY: html
html:
	$(MAKE)
	$(MAKE) -f Makefile.coq html COQDOCFLAGS="-interpolate -utf8 --parse-comments"
	osascript $(HOME)/s/tools/safari-reload.as

DSSSLOC = $(shell realpath ../../../dsss18/dw)
bcp:
	$(MAKE) -C $(DSSSLOC) bcp

.PHONY: tags
tags:
	$(MAKE) clean
	$(MAKE) -C $(DSSSLOC) clean
	-rm tags.tmp
	find . -name "*.v" >> tags.tmp
	find . -name "_Coq*" >> tags.tmp
	find $(DSSSLOC) -name "*.v" >> tags.tmp
	find $(DSSSLOC) -name "_Coq*" >> tags.tmp
	etags `cat tags.tmp`


### Dep graph

COQDEP=coqdep
DEPS_DOT=deps.dot
DEPS_OUT=deps.jpg

depgraph:
	$(COQDEP) -dumpgraph $(DEPS_DOT) -Q . DeepWeb Lib Spec Proofs Tests > /dev/null 2>&1
	sed 's%\("\([^"]*\)/\([^"/]*\)"\[label="\)%\1\2/\n%' -i deps.dot
	dot $(DEPS_DOT) -Tjpg -o$(DEPS_OUT)
