# Mappings and Updates

**Goal of this section**
Explain how Act handles **nested mappings** and **multi-party state updates**, using `allowance` and `transferFrom` as the motivating example.


## The Allowance Structure
ERC20 introduces delegated transfers through the `allowance` mapping:

```act
mapping(address => mapping(address => uint256)) allowance
```

This mapping records, for each token owner, how many tokens a *spender* is allowed to transfer on their behalf.

Conceptually, `allowance` is a function:
$(owner, spender) \mapsto approved amount$

In Act, this structure is represented directly as a nested mapping, rather than being encoded indirectly.

## Reading from Nested Mappings
Reading from nested mappings is written using chained indexing:
```act
allowance[from][CALLER]
```

This expression evaluates to the current allowance granted by `from` to the caller.
As with all mapping reads in Act:
- if no value has been explicitly written, the result is 0
- the read does not modify state


## The `transferFrom` Behaviour
The `transferFrom` behaviour allows the caller to transfer tokens from one address to another, subject to allowance.

*(excerpt from erc20.act)*
```act
behaviour transferFrom(address from, address to, uint256 value)
iff CALLVALUE == 0
```

As with `transfer`, the behaviour begins by restricting successful execution to calls that do not send Ether.

## Preconditions for Delegated Transfers
In addition to basic arithmetic safety, `transferFrom` must ensure:
- the sender has sufficient balance
- the caller has sufficient allowance

In Act, these requirements appear as explicit preconditions:

```act
inRange(uint256, balanceOf[from] - value)
inRange(uint256, balanceOf[to] + value)
inRange(uint256, allowance[from][CALLER] - value)
```

Each of these conditions mirrors a check performed implicitly by Solidity’s compiled code.
By writing them explicitly, Act makes it clear **exactly when** the behaviour is defined.

## Updating Multiple Mappings in One Step
The core of `transferFrom` is its storage update block:

```act
storage
  balanceOf := balanceOf[
    from => balanceOf[from] - value,
    to   => balanceOf[to]   + value
  ]

  allowance := allowance[
    from => allowance[from][
      CALLER => allowance[from][CALLER] - value
    ]
  ]
```

This block performs **three logically separate updates**:
1. Decrease the balance of from
2. Increase the balance of to
3. Decrease the caller’s allowance

All updates:
- are evaluated against the same initial state
- are applied simultaneously
- leave all other storage locations unchanged

## Why Updates Are Structured This Way
It is tempting to think of the updates as sequential steps, but that intuition is misleading.
Act intentionally avoids sequential semantics for storage updates because:
- order-dependent updates are difficult to reason about
- sequential updates obscure invariants
- the EVM itself does not expose a sequential state model at the specification level
By treating updates as equations over pre- and post-state, Act ensures that the behaviour is unambiguous and mathematically well-defined.

## Comparison with `transfer`
It is instructive to compare `transferFrom` with `transfer`:
- `transfer` updates two balances
- `transferFrom` updates two balances and one allowance
- both follow the same structure:
    - preconditions
    - case distinction if needed
    - simultaneous updates
This uniformity is intentional: once the reader understands one behaviour, the others follow the same pattern.

## What We Gain from Explicitness
By fully specifying `transferFrom`, the Act specification now makes explicit:
- all failure conditions
- all affected storage locations
- all arithmetic constraints

Nothing is implicit or left to the reader’s interpretation.

This explicitness is what enables Act to:
- check equivalence with EVM bytecode
- characterize all reachable states
- support reasoning over contract properties