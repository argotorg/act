# Contructors and Initial State

Constructors in act specify the initial state of contract storage and the conditions under which a contract can be successfully deployed.

## Constructor Structure

The general shape of a constructor in act is:

```
┌──────────────────────────────────────────────────────────────┐
│         constructor ?payable (<parameters>)                  │
└─────────────────────────┬────────────────────────────────────┘
                          │
                          ▼
                  ┌───────────────--┐
                  │ iff <condition> │
                  └────────┬────────┘
                           │
              ┌────────────┴────────────┐
              │                         │
              ▼                         ▼
      No branching                Branching (cases)
              │                         │
              ▼                         ▼
    ┌──────────────────────┐  ┌──────────────────────────┐
    │ creates              │  │ case <condition>:        │
    │   <storage_init>     │  │   creates <storage_init> │
    └──────────────────────┘  └──────────┬───────────────┘
                                         │
                                         ▼
                                        ...
                                        
                                         │
                                         ▼
                              ┌──────────────────────────┐
                              │ case <condition>:        │
                              │   creates <storage_init> │
                              └──────────────────────────┘
```

**Components:**

1. **Constructor Head**: `constructor ?payable (<parameters>)`
   - Optional `payable` keyword for accepting Ether during deployment.
   - Parameter list with types and names separated by commas.

2. **Precondition Block**: `iff <condition>`
   - Specifies the necessary and sufficient condition for successful constructor execution.
   - Must be present (use `iff true` if there are no preconditions).

3. **Cases Block** (optional):
   - If present, there are multiple `case <condition>: creates ...` branches whose conditions are mutually exclusive and exhaustive.
   - The absence of a cases block is equivalent to a single implicit `case true:` block.
   - The cases blocks allow the user to specify different storage initializations (`creates <storage_init>`) depending on which `condition` the constructor parameters meet. It mirrors the `if then else` structure in EVM smart contracts.

4. **Creates Block**: `creates <storage_init>`
   - Initializes storage variables with initial values
   - Every storage variable declared in the contract must be initialized in every `creates` block.
   - The assignments are separated by newlines and have the shape: `<type> <name> := <expression>`




## Payable and Non-Payable Constructors
In EVM smart contracts, constructors can be declared `payable` or non-payable (the default).
A `payable` constructor allows sending Ether along with contract creation, while a non-payable constructor rejects any Ether sent.
In act, the situation is similar: there is a keyword `payable` in the constructor declaration to mark payable constructors. For every constructor that is not marked `payable`, act automatically internally adds a precondition that no Ether is sent during construction.

Similarly, if a constructor is marked `payable`, the user has to declare and initialize the contract's balance in Ether using the special variable `uint256 BALANCE`. For non-payable constructors, `BALANCE` is set to `0` implicitly and the user does not have to declare or initialize it.

In the ERC20 example, the constructor is non-payable. Thus, it does not include the `payable` keyword nor the `BALANCE` variable:


*(constructor from [erc20.act](https://github.com/argotorg/act/blob/main/tests/hevm/pass/multisource/erc20/erc20.act))*

```act
constructor(uint256 _totalSupply)

iff true

creates

  uint256 totalSupply := _totalSupply
  mapping(address => uint) balanceOf :=  [CALLER => _totalSupply]
  mapping(address => mapping(address => uint)) allowance := []
``` 

An artificial example of a *payable* constructor would be:

```act
constructor payable ()

iff true

case CALLVALUE > 0 :
creates
    bool myFlag := true
    uint256 BALANCE := CALLVALUE

case CALLVALUE == 0 :
creates
    bool myFlag := false
    uint256 BALANCE := 0
```

act interally tracks the balance (in Ether) of each contract, including during construction. This is required to correctly reason about payable constructors. Although this `BALANCE` variable is not part of the contract storage per se, it can be affected by the behavior of the constructor or the transitions and is therefore initialized and updated the same way as storage slots. 

Further, the user can write conditions on the callvalue sent during construction using the special variable `CALLVALUE`. See e.g. the payable constructor example above.
Additionally to `BALANCE`, there are 4 such special variables (called environment variables) related to the call environment that the user can access as explained in [Variable References](./store_type.md#variable-references).

## Constructor Preconditions
Consider the following constructor from an automated market maker (AMM) contract:

*(constructor from [amm.act](https://github.com/argotorg/act/blob/main/tests/hevm/pass/multisource/amm/amm.act))*

```act
constructor(address<Token> t0, address<Token> t1)

iff
    t0 != t1

creates

    Token token0 := t0
    Token token1 := t1
```
It is a non-payable constructor that takes two parameters, `t0` and `t1`, which are addresses of ERC20 token contracts. The data type `address<Token>`, is called *annotated address type* and indicates that these addresses point to deployed contracts of type `Token` (i.e., ERC20 tokens) and is explained in [ABI Types](./store_type.md#abi-types).

The `iff` clause specifies the **necessary and sufficient condition** under which the constructor succeeds. If this condition does not hold, the constructor reverts.
In this example, the precondition `t0 != t1` ensures that the two token addresses are distinct. If a user attempts to deploy the AMM contract with identical token addresses, the constructor will revert, preventing the creation of an invalid AMM instance.

The precondition block extends the `require`/`assert` statements commonly used in Solidity/Vyper constructors by explicitly listing requirements that are implicit in the code. In the above case the `iff` block is the same as the `require`/`assert` statement in Solidity/Vyper: 

*(constructor from [amm.sol](https://github.com/argotorg/act/blob/main/tests/hevm/pass/multisource/amm/amm.sol))*

```solidity
 constructor(address t0, address t1) {
        require (t0 != t1);
        token0 = Token(t0);
        token1 = Token(t1);
    }
```

*(constructor from [amm.vy](https://github.com/argotorg/act/blob/main/tests/hevm/pass/multisource/amm/amm.vy))*

```vyper
@deploy
def __init__(t0: address, t1: address):
  assert (t0 != t1)
  self.token0 = Token(t0)
  self.token1 = Token(t1)
```


As mentioned before, the `iff` block cannot be skipped even if the condition is trivial, in which case the user should write `iff true` as shown in the ERC20 example.

### `inRange` in Preconditions
Whenever arithmetic operations are involved in the storage initialization, it is necessary to ensure that these operations do not overflow or underflow. This is done using the `inRange` expression ([Base Expressions](./store_type.md#base-expressions)), which checks whether a value fits within a specified type. In solidity these range checks are implicit, but in act they must be made explicit in the precondition block.

For example, consider a constructor that initializes a balance by subtracting a value from an initial amount. To ensure that this subtraction does not underflow, the precondition would include an `inRange` check:



```act
constructor(uint256 initialAmount, uint256 deduction)
iff
    inRange(uint256, initialAmount - deduction)
creates
    uint256 balance := initialAmount - deduction
```

The same principle applies to transitions and storage updates. How the arithmetic safety is enforced in act is explained in more detail in [Arithmetic Safety](./type_checking.md#1-arithmetic-safety).

## Initializing Storage

The storage is created in the `creates` block, where each storage variable is initialized as `<type> <name> := <expression>`. The allowed types and expressions are explained in [Storage, Typing and Expressions](./store_type.md). 

We revisit the storage initialization of the ERC20 constructor:

*(snippet from [erc20.act](https://github.com/argotorg/act/blob/main/tests/hevm/pass/multisource/erc20/erc20.act) constructor)*

```act
creates 
  uint256 totalSupply := _totalSupply
  mapping(address => uint) balanceOf :=  [CALLER => _totalSupply]
  mapping(address => mapping(address => uint)) allowance := []
```

**All** storage variables declared in the contract must be initialized in **every** `creates` block of the constructor. If the constructor is payable, the special variable `BALANCE` must also be declared and initialized. Here, the constructor initializes three storage variables and specifies their types:
- `totalSupply` of type `uint256`, initialized to the constructor parameter `_totalSupply`.
- `balanceOf`, which maps addresses to integers and therefore has type `mapping(address => uint)`. It is initialized such that the deployer (`CALLER`) receives the entire supply. Every other address is not mentioned and thus defaults to `0`.
- `allowance` maps pairs of addresses to integers and therefore has (the curried) type `mapping(address => mapping(address => uint))`. It initialized to an empty mapping (all values default to `0`).


This should be read as:
“In the initial state, the total supply of tokens is `totalSupply`, `balanceOf(CALLER) = totalSupply`, and all other addresses have `0`. Further `allowance(addr0, addr1) = 0` for all pairs of addresses.”

Note that the act spec describes only the end-result of the constructor execution, not the intermediate steps. 

## Constructors Cannot Modify Existing Contracts
An important design choice in act is that constructors:
- **may create new contracts**. E.g. `Token new_token := new Token(100)` could be used to create a new ERC20 contract with an initial supply of `100` and assign it to the storage variable `new_token`.
- **must initialize their own storage** (e.g.`uint256 totalSupply := _totalSupply` in the ERC20 example).
- **may not mutate existing contract storage**. I.e. only assigning existing contracts to storage variablesis allowed. E.g. `Token token0 := t0` as in the AMM constructor.
This restriction ensures that contract creation is local and predictable, and it plays a key role later when we reason about ownership and functional semantics.

For ERC20, this restriction is invisible — but it becomes crucial in more complex examples.