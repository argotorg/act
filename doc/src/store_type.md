# Storage, Typing and Expressions
In act, each contract explicitly declares its storage in the constructor and initializes it. The types of storage variables are explicit and checked. This section explains the storage model of act, the types allowed in storage, and the different kinds of expressions used throughout act specifications.

## Storage
In act, each contract explicitly declares its storage in the constructor and initializes it as defined in the source code. If the source code does not initialize a storage field, act uses defaults. For ERC20, the storage consists of two mappings and an integer:

*(snippet from [erc20.sol](https://github.com/argotorg/act/blob/main/tests/hevm/pass/multisource/erc20/erc20.sol), updates block)*

```solidity
    uint256 public totalSupply;
    mapping (address => uint256) public balanceOf;
    mapping (address => mapping (address => uint256)) public allowance;
```

The respective act declaration including initialization is:

*(corresponding snippet from [erc20.act](https://github.com/argotorg/act/blob/main/tests/hevm/pass/multisource/erc20/erc20.act), constructor block)*

```act, editable
creates
  uint256 totalSupply := _totalSupply
  mapping(address => uint256) balanceOf := [CALLER => _totalSupply]
  mapping(address => mapping(address => uint256)) allowance := []
```

For each storage variable its initialization has the shape `<type> <name> := <storage_expression>`. The act storage corresponds directly to the EVM state variables, but with two important differences:
1. All storage is immutable by default.
    Storage can only change through explicit updates inside transitions.
2. Types are explicit and checked. Which types storage can have is detailed next.


## Types
act has a rich type system to describe both storage and function parameters/return values. There are three main categories of types in act: 
- **Storage types**,
- **Mapping types**, and 
- **ABI types**.

### Storage Types (a.k.a. Slot Types)
Storage in act can have the following types:

- **base types** e.g. line 2 in the snippet above: `uint256 totalSupply`
    - unsigned integers of various sizes: `uint8`, `uint16`, `uint32`, `uint64`, `uint128`, `uint256`, 
    where `uint` is a shorthand for `uint256`.
    - signed integers of various sizes: `int8`, `int16`, `int32`, `int64`, `int128`, `int256`, 
    also `int` is a shorthand for `int256`.
    - booleans: `bool` 
    - addresses:`address`
- **mapping types** 
    - mappings from one base type to another, e.g. from `address` to `uint256` in line 3 `mapping(address => uint256) balanceOf`
    - nested mappings: from a base type to another mapping, e.g. from `address` to `mapping(address => uint256)` in line 4 `mapping(address => mapping(address => uint256)) allowance`
- **contract types**  referencing the storage of other contracts  (details in [Alasing and Unique Ownership](./aliasing.md))
    - A contract type `ContractType` can be used as a storage type to denote a reference to the storage of another contract of type `ContractType`.
    - This allows act specifications to model interactions between multiple contracts.
    - Artificial example: Another contract `OtherContract` uses in its storage a reference to an ERC20 `Token` contract: In `OtherContract`'s storage we would have a field of type `Token`, which can be initialized with (an address of) a specific deployed ERC20 contract instance. An example of this is shown in [Constructor Preconditions](./constructors.md#constructor-preconditions).


### Mapping Types and Defaults
A **mapping** in act behaves like a total function with a default value.
For example, the type:

```act
mapping(address => uint256) balanceOf
```

denotes a function from addresses to integers, where all keys not explicitly written map to the default value of `uint256`, which is `0`. If it is initialized as in line 3 of the constructor snippet above:

```act
mapping(address => uint256) balanceOf := [CALLER => _totalSupply]
```

then the mapping behaves like this:
- `balanceOf[CALLER]` evaluates to `_totalSupply`
- For any other address `A`, `balanceOf[A]` evaluates to `0`

The **defaults** for the different mapping types are:
- `uint*` and `int*`: `0`
- `bool`: `false`
- `address`: `0x00000000000000000000000000000000` which is the zero address.
- `mapping(<base type> => <mapping_type>)`: a mapping where all keys map to the default value of `<mapping_type>`. *Note: mapping types here include base types but **not** contract types.*

This matches Solidity’s behavior but is **made explicit** in act, which is essential for reasoning about invariants.

### ABI Types 

The following types are used for function parameters and return values, mirroring the Ethereum ABI specification:

-  All **base types** (`uint*`, `int*`, `bool`, `address`) are allowed here.
-  Additionally, there is another ABI type:  specially **annotated address types**. These are addresses which point to contracts. Intuitively, an annotated address type `address<ContractType>` can be thought of as a regular address, for which we know that it points to the storage of a contract of type `ContractType`. 

    Consider the following act snippet that declares a transition `foo` which takes an address of an ERC20 contract as parameter:

    ```act
    transition foo(address<Token> token_addr)
    iff true
    updates
        erc_token := address(token_addr)
    ```
    The parameter `token_addr` has type `address<Token>`, which indicates that the address points to a deployed contract of type `Token` (e.g. in our example an ERC20 token).
    
     This special type exists to allow act to reason about calls to this contract now called `erc_token`, which *lives* at address `token_addr` inside the transition body. Ensuring that the spec which includes this annotated address types is equivalent to the implementation which only uses regular addresses is still possible and discussed in [Input Space Equivalence](./equiv.md#input-space-equivalence).


    
*Note:* Not all types in act are allowed everywhere. There is a distinction between **ABI types** and **Storage types**:
1. **ABI types** include **base types** and **annotated address types**. They are used for function parameters and return values.
2. **Storage types** include **base types**, **mapping types**, and **contract types**. They are
 used for storage.

That means in function parameters and return values, mapping types and contract types are not allowed. Whereas in storage, annotated address types are not allowed.


## Expressions

Expressions appear throughout constructor and transition declarations: in preconditions (`iff` blocks), case conditions, storage initialization and updates (in `creates` and `storage` blocks) as well as in `return` statements of transitions. act distinguishes between three kinds of expressions, each serving different purposes:

### Overview of Expressions

1. **Storage Expressions (Slot Expressions)**: Expressions that manipulate storage data. Used in the `creates` and `updates` block to initialize or update storage variables. Examples in the ERC20 constructor: `_totalSupply`, `[CALLER => _totalSupply]`, `[]`, `new Token(100)`.

2. **References**: Variable references that denote storage locations or calldata. Used in preconditions, case conditions, and to reference existing values (as it is done in storage updates). Examples in the ERC20: `totalSupply`, `balanceOf[CALLER]`, `CALLVALUE`, `allowance`.

3. **Base Expressions**: Composite expressions built from operators and literals. Include arithmetic, boolean logic, comparisons, and conditionals. Used in all contexts (preconditions, cases, storage, returns). Examples: `x + y`, `true`, `x == 5`, `if z > 0 then a else b`.

### Storage Expressions

Storage expressions describe the initial values assigned to storage variables in the `creates` block and the values they are updated to in the `updates` block. The syntax for initializing in the `creates` block is `<type> <name> := <storage_expression>`. For updating in the `updates` block, it is `<name> := <storage_expression>`.
Storage expressions can be:

- **Base Expressions**: literals, composed expressions  or certain Variable References: `100`, `x + y`, `if condition then a else b`. See Base Expressions below for details.
- **Mappings**: Expressions that have mapping typ. The syntax of **defining new mappings** is the following:
    - `[<key1> => <value1>, <key2> => <value2>, ...]` (a mapping with multiple entries)
    - `[]` (an empty mapping where all keys map to the default value)
Every key not explicitly mentioned maps to the default value of the mapping's value type.
Further, exists the syntax for **adapting mappings** (used in `updates` blocks of transitions):
    - `my_map[my_key => my_value]` (defines a mapping, where  `my_key` maps to `my_value` and every other key has value `my_map[key]`)
    - similarly, multple entries can be changed at once: `my_map[key1 => value1, key2 => value2,...]`
- **Contract creation**: An instance of another contract (an ERC20 `Token` for example) can be part of a contract's storage. The corresponding storage expression is `new Token(100)`. It creates a new ERC20 contract instance with total supply 100. The keyword `new` indicates that a new contract instance is created. The parentheses contain the arguments passed to the constructor of the other contract.

    Depending on whether this other contract's constructor is `payable` or not (see [Payable and Non-Payable Constructors](./constructors.md#payable-and-non-payable-constructors)), the storage expression requires to specify the amount of Ether to send.
    - For a non-payable constructor, no Ether is sent and therefore nothing extra has to be specified. Hence `new Token(100)` suffices.
    - For a payable constructor, the amount of Ether to send must be specified. Assume there is a payable constructor `TokenPayable`, then the storage expression would be e.g. `new TokenPayable{value:10}(100)` to create a new instance of `TokenPayable` with initial supply `100` and send `10` wei during construction. The keyword to specify the amount of Ether (wei) to send is `value`.
- **references to existing contracts**: `erc_token` (a reference to a deployed contract instance)
- **Addresses of existing contracts**: `token_addr` (an address of a deployed contract instance)


**Example from the ERC20 contract:**

In the ERC20 constructor, the storage is initialized as:
 
*(snippet from [erc20.act](https://github.com/argotorg/act/blob/main/tests/hevm/pass/multisource/erc20/erc20.act), constructor block)*

```act
creates
  uint256 totalSupply := _totalSupply
  mapping(address => uint) balanceOf := [CALLER => _totalSupply]
  mapping(address => mapping(address => uint)) allowance := []
```

Here we see:
- A base expression: `_totalSupply`
- A new mapping: `[CALLER => _totalSupply]` which assigns the entire supply to the caller and defaults to 0 for all other addresses
- An new empty mapping: `[]` where all addresses map to the default map from `address` to `uint`, which is `0`.

In a transfer transition of the ERC20 contract the storage is updated as:

*(snippet from [erc20.act](https://github.com/argotorg/act/blob/main/tests/hevm/pass/multisource/erc20/erc20.act), transfer transition)*
```act
  updates

    balanceOf := balanceOf[ CALLER => balanceOf[CALLER] - _value
                          , to     => balanceOf[to] + _value]

```

Here we see a base expression, variable references (`CALLER` and `to`), a parameter `_value`, subtraction and addition.





### Variable References

References denote storage locations or parameters and are used as building blocks in:
- **Preconditions** (`iff` blocks): e.g., `t0 != t1`
- **Case conditions**: e.g., `case CALLVALUE > 0:`
- **Storage updates in transitions**: (covered in the Transitions section)

Basic references include:
- **Storage Variable names**: `totalSupply`, `balanceOf`, `allowance`
- **Parameter names**: `_totalSupply`, `to`, `value`
- **Environment variables**: `CALLER`, `CALLVALUE`, `ORIGIN`, `THIS`, `BALANCE`
    Environment variables represent special values provided by the EVM:
    - `address CALLER`: the address of the entity (externally owned account or contract)
        that invoked the current function.
    - `uint256 CALLVALUE`: the amount of Ether (in wei) sent with the current call.
    - `addresss ORIGIN`: the address of the original external account that started the transaction.
    - `address THIS`: the address of the current contract.
    - `uint256 BALANCE`: the balance of the current contract in Ether. 
- **Mapping references**: `balanceOf[CALLER]`
- **Field references**:  `t0.balanceOf` (if `t0` is a contract reference)

**Example from ERC20 transfer transition:**

The preconditions in the transfer transition use references:

*(snippet from transfer transition in [erc20.act](https://github.com/argotorg/act/blob/main/tests/hevm/pass/multisource/erc20/erc20.act))*

```act
iff
  inRange(uint256, balanceOf[CALLER] - value)
  CALLER != to ==> inRange(uint256, balanceOf[to] + value)

```

The precondition uses the mapping references `balanceOf[CALLER]` and `balanceOf[to]`, the parameter names `value`, and `to`, and the environment variable `CALLER`. The precondition ensures that the transfer does not cause an underflow or overflow in the balances.

### Base Expressions

Base expressions are composite expressions built using operators, literals and variable references of certain types. They are used wherever an expression is needed: in preconditions, case conditions, during storage initialization and updates, and in return statements.

**Arithmetic operators** (for integer types):
- Addition: `x + y`
- Subtraction: `x - y`
- Multiplication: `x * y`
- Division: `x / y`
- Modulo: `x % y`
- Exponentiation: `x ^ y`

**Boolean operators**:
- Conjunction: `condition1 and condition2`
- Disjunction: `condition1 or condition2`
- Negation: `not condition`
- Implication: `condition1 ==> condition2`

**Comparison operators** (work on all types):
- Equality: `x == y`
- Inequality: `x != y`
- Less than: `x < y`
- Less than or equal: `x <= y`
- Greater than: `x > y`
- Greater than or equal: `x >= y`

**Other operators**:
- Conditionals: `if condition then expr1 else expr2`
- Range checks: `inRange(uint256, x)` (checks if `x` fits in the given type) See [Preconditions](./constructors.md#constructor-preconditions) and [Arithmetic Safety](./type_checking.md#1-arithmetic-safety) for details.

**Literals and Other Expressions**:
- Literals: `5`, `true`, `false`
- Variable references of ABI types (integers, booleans, addresses, and annotated address type `address<ContractType>`), e.g. `totalSupply`, `CALLER`, `value`

  Whenever an expression `expr` of annotated address type is seen as a regular address (e.g. when used in arithmetic), it has to be cast to a regular `address` type using `address(expr)`.
- Address conversion of deployed contracts: `addr(t0)` (if `t0` is a contract reference)

**Examples of Base Expressions**:

Consider the following `case` blocks from the `transferFrom` transition of the ERC20 contract:

*(snippet from transferFrom transition in [erc20.act](https://github.com/argotorg/act/blob/main/tests/hevm/pass/multisource/erc20/erc20.act))*

```act
transition transferFrom(address src, address dst, uint amount) : uint256

iff
    ...

case src != dst and CALLER == src:
    ...

case src != dst and CALLER != src and allowance[src][CALLER] == 2^256 - 1:
    ...

case src != dst and CALLER != src and allowance[src][CALLER] < 2^256 - 1:
    ...

case src == dst and CALLER != src and allowance[src][CALLER] < 2^256 - 1:
    ...

case src == dst and (CALLER == src or allowance[src][CALLER] == 2^256 - 1):
    ...

```

Here, various base expressions with exponentiations, comparisons and boolean operators are used. Moreover, variable references like `allowance[src][CALLER]`, `src`, `dst`, and `CALLER` are used to build these expressions.

