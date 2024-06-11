all:
	coq_makefile -f _CoqProject -o Makefile.coq
	## This part is broken because recursive definitions don't work.
	# cn --lemmata=theories/ExportedDefinitions.v ../list_rev.c
	make -f Makefile.coq

