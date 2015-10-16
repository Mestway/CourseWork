V=$(wildcard *.v)
VOBJ=$(patsubst %.v,%.vo,$(V))

COQC=coqc

all: $(VOBJ)

%.vo: %.v
	$(COQC) $<

include Makefile.coq
