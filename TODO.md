Implementation TODOs

Target release data: 15/1/2025

- Usability 
  - [ ] Multiple files with nice error messages
  - [ ] Ordering of contracts in multiple files in DAG order

- Parser
  - [ ] New syntax

- Typing
  - [ ] New typechecker (WIP)
  - [ ] Entailment check
  - [ ] Correct handling of Eth environment vars + balance

- HEVM
  - [ ] Merge environment PR
  - [ ] Constructor Cases
  - [ ] Equivalence checking time (AMM?)
  - [ ] Clean up? 
  - [ ] Correct handling of Eth environment vars + balance


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

- Callvalue must subtract from balance!!!




balance := balance - 10 