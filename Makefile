.DEFAULT_GOAL := compiler
.PHONY: parser compiler docs

parser: src/Act/Lex.hs src/Act/Parse.hs

src/Act/Parse.hs: src/Act/Parse.y src/Act/Syntax/Untyped.hs
	happy src/Act/Parse.y

src/Act/Lex.hs: src/Act/Lex.x
	alex src/Act/Lex.x

# builds the rest of the haskell files (compiler)
bin/act: src/CLI/*.hs src/Act/*.hs
	cabal v2-install --installdir=bin --overwrite-policy=always

repl: src/Act/Lex.hs src/Act/Parse.hs
	cabal v2-repl

compiler: bin/act

docs:
	cd doc && mdbook build

docs-serve:
	cd doc && mdbook serve

frontend_pass=$(wildcard tests/typing/pass/*/*.act)
frontend_fail=$(wildcard tests/typing/fail/*/*.act)

parser_pass=$(filter-out $(failing_parser), $(frontend_pass))
typing_pass=$(filter-out $(failing_typing), $(frontend_pass))

# supposed to fail
parser_fail=$(filter-out $(typing_fail), $(frontend_fail))
typing_fail=$(filter-out $(passing_typing), $(frontend_fail))

# supposed to pass, but fail
failing_parser=tests/typing/pass/dss/vat.act
failing_typing=tests/typing/pass/dss/vat.act tests/typing/pass/creation/createMultiple.act tests/typing/pass/staticstore/staticstore.act
# supposed to fail, but pass
passing_typing=tests/typing/fail/array/out_of_bounds_inv.act tests/typing/fail/array/out_of_bounds_post.act

invariant_specs=$(wildcard tests/invariants/*/*.act)
invariant_pass=$(filter-out $(invariant_buggy), $(wildcard tests/invariants/pass/*.act) $(typing_pass))
invariant_fail=$(wildcard tests/invariants/fail/*.act)

postcondition_specs=$(wildcard tests/postconditions/*/*.act)
postcondition_pass=$(wildcard tests/postconditions/pass/*.act) $(typing_pass)
postcondition_fail=$(wildcard tests/postconditions/fail/*.act)

# supposed to pass, but timeout
hevm_buggy=tests/hevm/pass/transfer/transfer.act tests/hevm/pass/multisource/amm/sol_vyper.json tests/hevm/pass/multisource/amm/vyper_sol.json tests/hevm/pass/cast-3/cast-3.act
# supposed to pass
hevm_pass=$(filter-out $(hevm_buggy), $(wildcard tests/hevm/pass/*/*.act))
hevm_vy_pass=$(wildcard tests/hevm/pass/vyper/*/*.act)
hevm_multi_pass=$(filter-out $(hevm_buggy), $(wildcard tests/hevm/pass/multisource/*/*.json))
# supposed to fail
hevm_fail=$(wildcard tests/hevm/fail/*/*.act)
# supposed to pass
hevm_slow=tests/hevm/pass/amm/amm.act tests/hevm/pass/amm-2/amm-2.act
hevm_multi_slow=$(wildcard tests/hevm/pass/multisource/amm/*.json) $(wildcard tests/hevm/pass/multisource/erc20/*.json)
# supposed to pass, no slow tests
hevm_fast=$(filter-out $(hevm_slow), $(hevm_pass))
hevm_multi_fast=$(filter-out $(hevm_multi_slow), $(hevm_multi_pass))


#coq-examples = tests/coq/multi tests/coq/transitions tests/coq/safemath tests/coq/exponent tests/coq/token tests/coq/ERC20-simple tests/coq/ERC20  tests/coq/amm tests/coq/pointers

.PHONY: test-coq $(coq-examples)
test-coq: compiler $(coq-examples)
$(coq-examples):
	make -C $@ clean
	make -C $@

test-parse: parser compiler $(parser_pass:=.parse.pass) $(parser_fail:=.parse.fail)
test-type: parser compiler $(typing_pass:=.type.pass) $(typing_fail:=.type.fail)
test-invariant: parser compiler $(invariant_pass:=.invariant.pass) $(invariant_fail:=.invariant.fail)
test-postcondition: parser compiler $(postcondition_pass:=.postcondition.pass) $(postcondition_fail:=.postcondition.fail)
test-hevm: parser compiler $(hevm_pass:=.hevm.pass) $(hevm_vy_pass:=.hevm.vy.pass) $(hevm_multi_pass:=.hevm.multi.pass) $(hevm_fail:=.hevm.fail)
test-hevm-fast: parser compiler $(hevm_fast:=.hevm.pass.fast) $(hevm_vy_pass:=.hevm.vy.pass) $(hevm_multi_fast:=.hevm.multi.pass) $(hevm_fail:=.hevm.fail)
test-cabal: src/*.hs
	cabal v2-run test

# Just checks parsing
tests/%.parse.pass:
	./bin/act parse --file tests/$* > tests/$*.parsed.hs
	diff tests/$*.parsed.hs.out tests/$*.parsed.hs
	rm tests/$*.parsed.hs

tests/%.parse.fail:
	./bin/act parse --file tests/$* && exit 1 || echo 0

tests/%.type.pass:
	./bin/act type --file tests/$* | jq . > tests/$*.typed.json
	diff tests/$*.typed.json.out tests/$*.typed.json
	rm tests/$*.typed.json.out

tests/%.type.fail:
	./bin/act type --file tests/$* && exit 1 || echo 0

tests/%.invariant.pass:
	./bin/act prove --file tests/$*
	./bin/act prove --solver cvc5 --file tests/$*

tests/%.invariant.fail:
	./bin/act prove --file tests/$* && exit 1 || echo 0
	./bin/act prove --solver cvc5 --file tests/$* && exit 1 || echo 0

tests/%.postcondition.pass:
	./bin/act prove --file tests/$*
	./bin/act prove --solver cvc5 --file tests/$*

tests/%.postcondition.fail:
	./bin/act prove --file tests/$* && exit 1 || echo 0
	./bin/act prove --solver cvc5 --file tests/$* && exit 1 || echo 0

tests/hevm/pass/%.act.hevm.pass:
	$(eval CONTRACT := $(shell awk '/contract/{ print $$2 }' tests/hevm/pass/$*.sol))
	./bin/act hevm --spec tests/hevm/pass/$*.act --sol tests/hevm/pass/$*.sol --solver bitwuzla --smttimeout 100000000

tests/hevm/pass/%.act.hevm.vy.pass:
	$(eval CONTRACT := $(shell awk '/contract/{ print $$2 }' tests/hevm/pass/$*.vy))
	./bin/act hevm --spec tests/hevm/pass/$*.act --vy tests/hevm/pass/$*.vy --solver bitwuzla --smttimeout 100000000

tests/hevm/pass/%.json.hevm.multi.pass:
	./bin/act hevm --sources tests/hevm/pass/$*.json --solver bitwuzla --smttimeout 100000000

tests/hevm/fail/%.act.hevm.fail:
	$(eval CONTRACT := $(shell awk '/contract/{ print $$2 }' tests/hevm/fail/$*.sol))
	./bin/act hevm --spec tests/hevm/fail/$*.act --sol tests/hevm/fail/$*.sol --solver bitwuzla && exit 1 || echo 0

tests/hevm/pass/%.act.hevm.pass.fast:
	$(eval CONTRACT := $(shell awk '/contract/{ print $$2 }' tests/hevm/pass/$*.sol))
	./bin/act hevm --spec tests/hevm/pass/$*.act --sol tests/hevm/pass/$*.sol --solver bitwuzla --smttimeout 100000000

test-ci: test-parse test-type test-invariant test-postcondition test-coq test-hevm-fast
test: test-ci test-cabal
