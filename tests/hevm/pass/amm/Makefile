.PHONY: verify
verify: CoqMakefile amm_coq.v
	make -f CoqMakefile

amm_coq.v: amm.act
	act coq --file amm.act > amm_coq.v

CoqMakefile: _CoqProject
	coq_makefile -f _CoqProject -o CoqMakefile

.PHONY: clean
clean:
	if [[ -f CoqMakefile ]]; then make -f CoqMakefile clean; fi
	rm -f StateMachine.v CoqMakefile CoqMakefile.conf
	rm -f *.glob *.vo *.vok *.vos
