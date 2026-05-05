.PHONY: verify
verify: admin.lean
	lake env lean admin.lean -D linter.unusedVariables=false

admin.lean: admin.act
	act lean --file admin.act --solver z3 > admin.lean

.PHONY: clean
clean:
	rm -f admin.lean 