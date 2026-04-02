.PHONY: verify
verify: AMM.lean
	lake env lean AMM.lean -D linter.unusedVariables=false

AMM.lean: amm.act
	act lean --json amm.json --solver z3 > AMM.lean

.PHONY: clean
clean:
	rm -f AMM.lean 
