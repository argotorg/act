# Contructors and Initial State

**Goal of this section**

Show how Act specifies contract creation and the initial state, using ERC20’s minting logic.

## Constructor Preconditions
The ERC20 constructor requires that no Ether is sent along with deployment:

*(excerpt from erc20.act)*

```act
constructor(uint256 totalSupply)
iff CALLVALUE == 0
```

The `iff` clause specifies the **necessary and sufficient condition** under which the constructor succeeds. If this condition does not hold, the constructor reverts.
This mirrors Solidity’s `nonpayable` constructors, but makes the condition explicit.

## Initializing Storage
The constructor initializes the balanceOf mapping by assigning the entire supply to the deployer:

```act
storage
  balanceOf := [ CALLER => totalSupply ]
```

This should be read as:
“In the initial state, `balanceOf(CALLER) = totalSupply`, and all other addresses have balance `0`.”
No other storage locations are modified.

## Constructors Cannot Modify Existing Contracts
An important design choice in Act is that constructors:
- may create new contracts
- may initialize their own storage
- may not mutate existing contract storage
This restriction ensures that contract creation is local and predictable, and it plays a key role later when we reason about ownership and functional semantics.

For ERC20, this restriction is invisible — but it becomes crucial in more complex examples.