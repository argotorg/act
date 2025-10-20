.PHONY: verify
verify: RocqMakefile POINTERS.v
	make -f RocqMakefile

POINTERS.v: pointers.act
	act coq --file pointers.act > POINTERS.v

RocqMakefile: _CoqProject
	rocq makefile -f _CoqProject -o RocqMakefile

.PHONY: clean
clean:
	if [[ -f RocqMakefile ]]; then make -f RocqMakefile clean; fi
	rm -f POINTERS.v RocqMakefile RocqMakefile.conf
	rm -f *.glob *.vo *.vok *.vos
