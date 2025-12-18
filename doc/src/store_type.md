# Storage and Typing

**Goal of this section**
Explain how state is represented in Act, using ERC20 storage as the concrete example.


## Declaring Storage
In Act, each contract explicitly declares its persistent storage. For ERC20, this consists of two mappings:

*(excerpt from erc20.act, storage block)*

```act
storage
  mapping(address => uint256) balanceOf
  mapping(address => mapping(address => uint256)) allowance
```

This corresponds directly to the Solidity state variables, but with two important differences:
1. All storage is immutable by default
    Storage can only change through explicit updates inside behaviours.
2. Types are explicit and checked
    Act distinguishes between:
    - base types (uint256, bool, address)
    - mapping types
    - contract types (introduced later)

## Mapping Types and Defaults
A mapping in Act behaves like a total function with a default value.
For example, the type:

```act
mapping(address => uint256)
```

denotes a function from addresses to integers, where all keys not explicitly written map to 0.
This matches Solidity’s behavior but is **made explicit** in Act, which is essential for reasoning about invariants.

## ABI Types vs Storage Types
Not all types in Act are allowed everywhere:
- ABI types
    Used for function parameters and return values (e.g. uint256, address)
-  Storage types
    Used for persistent state
    (e.g. mappings, contract references)
    
For ERC20, all parameters and storage fields are ABI-compatible, which simplifies the specification. More complex contracts may involve non-ABI storage types.