Implementation TODOs

Target release data: 15/1/2025

- Usability 
  - [ ] Multiple files with nice error messages
  - [ ] Ordering of contracts in multiple files in DAG order

- Parser
  - [X] New syntax
  - [ ] CALLVALUE == 0 implicit when constructor/behv non-payable
  - [ ] Parsing -1 does not work

- Typing
  - [X] New typechecker
  - [ ] Entailment check (WIP)
  - [ ] Correct handling of Eth environment vars + balance

- HEVM
  - [X] Merge environment PR
  - [ ] Constructor Cases (WIP)
  - [ ] Equivalence checking time (AMM?)
  - [ ] Clean up? 
  - [ ] Correct handling of Eth environment vars + balance
  - [ ] Signed Integer overflow


- Rocq
  - [ ] Consistent predicate
  - [ ] Correct handling of Eth environment vars + balance


- Examples
  - AMM time out? 
  - Tests for new features 
    - [ ] balance and callvalue
    - [ ] other Eth env
    - Constructor cases
  - Maybe cleanup test directory
  - Add example with non-local side effects for transitions

- Think about: 

  - constructor (addr a) {
      a.send(10);
    }

- Callvalue must subtract from balance!!!




balance := balance - 10 
