.PHONY: all clean install

all: Makefile.coq
	$(MAKE) -f Makefile.coq

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq Makefile.coq.conf

install: Makefile.coq
	$(MAKE) -f Makefile.coq install

Makefile.coq: _CoqProject
	rocq makefile -f _CoqProject -o Makefile.coq
