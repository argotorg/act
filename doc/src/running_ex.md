# A First Look: ERC20 as Running Example

In this section, we present a first look at an act specification by walking through a simple example: an ERC20 token contract. The goal is to illustrate the overall structure of an act specification and how it relates to the underlying smart contract code.

## From EVM Smart Contract to act
We start from an ERC20-style contract written in Solidity respectively Vyper:

*(code snippets from [erc20.sol](https://github.com/argotorg/act/blob/main/tests/hevm/pass/multisource/erc20/erc20.sol) and [erc20.vy](https://github.com/argotorg/act/blob/main/tests/hevm/pass/multisource/erc20/erc20.vy); storage and function signatures only)*

```solidity
contract Token {
    uint256 public totalSupply;
    mapping(address => uint256) public balanceOf;
    mapping(address => mapping(address => uint256)) public allowance;

    constructor(uint256 _totalSupply);
    function transfer(address to, uint256 value) public;
    function transferFrom(address from, address to, uint256 value) public;
    ...
}
```

```vyper
  totalSupply: public(uint256)
  balanceOf: public(HashMap[address, uint256])
  allowance: public(HashMap[address, HashMap[address, uint256]])

  @deploy
  def __init__(_totalSupply: uint256)
  @external
  def transfer(value_: uint256, to: address) -> bool
  @external
  def transferFrom(from_: address, to: address, value_: uint256) -> bool
  ...
``` 

  <!-- function approve(address spender, uint256 value) public;
  function burn(uint256 value) public;
  function burnFrom(address account, uint256 value) public;
  function mint(address account, uint256 value) public; -->


> An **ERC20 token** is a standard type of smart contract on Ethereum that represents a fungible asset, meaning all units of the token are interchangeable (like dollars or euros, rather than NFTs). The contract maintains a ledger that records how many tokens each address owns and provides a small, fixed interface for moving tokens between addresses. The core piece of state is the `balanceOf` mapping, which assigns to every address its current token balance; the sum of all balances represents the total supply of the token. 
>
> A token holder can move tokens directly using `transfer`, which subtracts a specified amount from the caller’s balance and adds it to the recipient’s balance, provided the caller has sufficient funds. 
>
> In addition to direct transfers, ERC20 supports delegated transfers through the `allowance` mechanism: an address can authorize another address (a “spender”) to transfer up to a certain number of tokens on its behalf. These authorizations are recorded in the `allowance` mapping, which maps an owner and a spender to an approved amount. The `transferFrom` function uses this mechanism to move tokens from one address to another while decreasing both the owner’s balance and the remaining allowance of the spender. Together, `balanceOf`, `allowance`, `transfer`, and `transferFrom` define a simple but powerful accounting model that enables tokens to be held, transferred, and used by third-party contracts without giving them unrestricted control over a user’s funds.

An **act specification** describes the **externally observable behavior** of this contract. At a high level, an act specification consists of one or more contracts, where each contract has:
- a **constructor**, describing what storage is created and how it is initialized
- a set of **transitions**, one for each callable function
- explicit **preconditions** under which function calls succeed
- explicit **storage updates** describing the resulting state


## The Shape of an act Contract
The translation of the code above into an act specification has the following top-level structure:

*(snippet from [erc20.act](https://github.com/argotorg/act/blob/main/tests/hevm/pass/multisource/erc20/erc20.act), headers only)*

```act,editable 
contract Token:

constructor(uint256 _totalSupply)
iff true
    ...
creates
  uint256 totalSupply := _totalSupply
  mapping(address => uint) balanceOf :=  [CALLER => _totalSupply]
  mapping(address => mapping(address => uint)) allowance := []

transition transfer(uint256 value, address to)
iff true
    ...
case CALLER != to:
  updates
    ...
case CALLER == to:
  updates
    ...

transition transferFrom(address from, address to, uint256 value)
iff true
...
```

Even without understanding the details, several aspects are already visible:
- For each contract the act spec starts with `contract <NAME>:`.
- Afterwards the constructor `contructor(<input_vars>)` follows.
- Lastly all smart contract functions are listed as transitions `transition <fct_name>(<input_vars>)`
- Within the constructor and the transitions:
  - The list of preconditions (the `iff` block) comes first and lists the necessary and sufficient conditions on when this operation succeeds. If the `iff` block is not satisfied, the corresponding function in Solidity/Vyper would revert.
  - In the constructor the `creates` block is next. It lists all the storage a contract has and initializes it. As expected, it mirrors the Solidity/Vyper code closely. The `creates` block is the last block of the constructor.
  - Similar to `creates` for constructors works the `updates` block for transitions. It updates all the changes to the storage. Thereby, summarizing the effects a transition has on the storage.
  - If there are any branches in the underlying Solidity/Vyper code, then act distinguishes what happens to the storage relative to a `case`. In the ERC20 example, that happens in line 14 and line 17: depending on whether the function caller `CALLER` is the same address as the one where the money is supposed to be transfered to, `to`, the storage is updated differently.
- act is aware of some Ethereum environment variables such as the caller of a function `CALLER` or the amount that was "paid" to a contract upon a function call `CALLVALUE`.

In the next sections, we will build up the meaning of these pieces by incrementally refining the ERC20 specification.

Jump to [Running the ERC20 Example](./layout_tooling.md#running-the-erc20-example) if you want to try out running the ERC20 example with verification backends.

<!-- - act specifications are declarative: they describe what must hold, not how to execute.
- Each transition explicitly states when it is defined (iff ...).
- Storage updates are separated from control flow. -->

