.PHONY: verify
verify: ERC20.lean
	lake env lean ERC20.lean -D linter.unusedVariables=false

ERC20.lean: erc20.act
	act lean --file erc20.act --solver z3 > ERC20.lean

.PHONY: clean
clean:
	rm -f ERC20.lean 
