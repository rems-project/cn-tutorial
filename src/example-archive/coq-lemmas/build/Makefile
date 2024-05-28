


all:
	coq_makefile -f _CoqProject -o Makefile.coq
	cn ../../SantiagosExamples/trivial-lemma.c --lemmata theories/Gen_Spec.v
	make -f Makefile.coq

