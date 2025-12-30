# Arithmetic Safety

**Goal of this section**
Explain why Act requires explicit arithmetic bounds and how this relates to Solidity semantics.

## Checked Arithmetic Is Explicit in Act
Solidity performs checked arithmetic by default: overflows and underflows cause a revert.
In Act, these checks must be stated explicitly using `inRange`.
For ERC20 transfer, we require:

```act
inRange(uint256, balanceOf[CALLER] - value)
inRange(uint256, balanceOf[to] + value)
```

These conditions ensure that the subtraction and addition are valid `uint256` operations.


## Why This Is Necessary
Act specifications are checked against EVM bytecode. The EVM does not enforce arithmetic safety by itself — this behavior is a property of the compiled code.

By writing `inRange` explicitly, the specification:
- matches the compiled behavior precisely
- makes all failure conditions explicit
- prevents unsound reasoning about arithmetic


## Failure Is Explicit and Local
If an `inRange` condition fails, the behaviour reverts and no storage updates occur.
This aligns with Solidity’s execution model and allows Act to precisely characterize the contract’s input space.

*KIM to also briefly list supported logic and arithmetic*