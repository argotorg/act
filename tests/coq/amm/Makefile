.PHONY: verify
verify: RocqMakefile AMM.v
	make -f RocqMakefile

AMM.v: amm.act
	act coq --file amm.act > AMM.v

RocqMakefile: _CoqProject
	rocq makefile -f _CoqProject -o RocqMakefile

.PHONY: clean
clean:
	if [[ -f RocqMakefile ]]; then make -f RocqMakefile clean; fi
	rm -f AMM.v RocqMakefile RocqMakefile.conf
	rm -f *.glob *.vo *.vok *.vos
