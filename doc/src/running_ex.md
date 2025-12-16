# A First Look: ERC20 as Running Example

**Goal of this section**

Give the reader an intuition for what an Act specification looks like and how it relates to Solidity, without explaining every construct yet.

## From Solidity to Act (at a Glance)
We start from a familiar ERC20-style contract written in Solidity:

*(excerpt: function signatures only)*

```solidity
contract Token {
    mapping(address => uint256) public balanceOf;
    mapping(address => mapping(address => uint256)) public allowance;

    constructor(uint256 totalSupply);
    function transfer(address to, uint256 value) public;
    function transferFrom(address from, address to, uint256 value) public;
}
```


An Act specification describes the **externally observable behavior** of this contract. At a high level, an Act contract consists of:
- a constructor, describing how storage is initialized
- a set of behaviours, one for each externally callable function
- explicit preconditions under which calls succeed
- explicit storage updates describing the resulting state


## The Shape of an Act Contract
Here is the top-level structure of the ERC20 Act specification:

*(excerpt from erc20.act, headers only)*

```act 
contract Token:

constructor(uint256 totalSupply)
iff CALLVALUE == 0
storage
  ...

behaviour balanceOf(address owner)
returns uint256
iff CALLVALUE == 0
  ...

behaviour transfer(uint256 value, address to)
iff CALLVALUE == 0
  ...

behaviour transferFrom(address from, address to, uint256 value)
iff CALLVALUE == 0
  ...
```

Even without understanding the details, several features are already visible:
- Act specifications are declarative: they describe what must hold, not how to execute.
- Each behaviour explicitly states when it is defined (iff ...).
- Storage updates are separated from control flow.
In the next sections, we will build up the meaning of these pieces by incrementally refining the ERC20 specification.