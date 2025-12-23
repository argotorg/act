# Storage and Typing

**Goal of this section**
Explain how an EVM state is represented in Act, using ERC20 storage as the concrete example.


## Declaring Storage
In Act, each contract explicitly declares its persistent storage in the constructor and initializes it as defined in the source code. If the source code does not initialize a storage field, it uses defaults. For ERC20, the storage consists of two mappings and an integer:

*(snippet from erc20.sol, storage block)*

```solidity
    uint256 public totalSupply;
    mapping (address => uint256) public balanceOf;
    mapping (address => mapping (address => uint256)) public allowance;
```

The respective Act declaration including initialization is:

*(corresponding snippet from erc20.act, constructor block)*

```act, editable
creates
  uint256 totalSupply := _totalSupply
  mapping(address => uint256) balanceOf := [CALLER => _totalSupply]
  mapping(address => mapping(address => uint256)) allowance := []
```

The Act storage corresponds directly to the EVM state variables, but with two important differences:
1. All storage is immutable by default.
    Storage can only change through explicit updates inside transitions.
2. Types are explicit and checked. Which types storage can have is detailed next.

### Storage Types
Storage in Act can have the following types:

- **base types** e.g. line 2 in the snippet above: `uint256 totalSupply`
    - unsigned integers of various sizes: `uint8`, `uint16`, `uint32`, `uint64`, `uint128`, `uint256`, 
    - signed integers of various sizes: `int8`, `int16`, `int32`, `int64`, `int128`, `int256`, 
    - booleans: `bool` 
    - addresses:`address`
- **mapping types** 
    - mappings from one base type to another, e.g. from `address` to `uint256` in line 3 `mapping(address => uint256) balanceOf`
    - nested mappings: from a base type to another mapping, e.g. from `address` to `mapping(address => uint256)` in line 4 `mapping(address => mapping(address => uint256)) allowance`
- **contract types**  referencing the storage of other contracts  (details later in
    <span  style="color:red">
    "Advanced Topics: Aliasing and Unique Ownership" (?)
    </span>).   

    - Artificial example: Another contract `OtherContract` uses in its storage a reference to an ERC20 `Token` contract: In `OtherContract`'s storage we would have a field of type `Token`, which can be initialized with an address of a specific deployed ERC20 contract.~


## Mapping Types and Defaults
A **mapping** in Act behaves like a total function with a default value.
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

This matches Solidity’s behavior but is **made explicit** in Act, which is essential for reasoning about invariants.

## ABI Types 

The following types are used for function parameters and return values, mirroring the Ethereum ABI specification:

-  All **base types** (`uint*`, `int*`, `bool`, `address`) are allowed here.
-  Additionally, there is another ABI type:  specially **annotated address types**. These are addresses which point to contracts. Intuitively, an annotated address type `address<ContractType>` can be thought of as a regular address, for which we know that it points to the storage of a contract of type `ContractType`. 

    Consider the following act snippet that declares a transition `foo` which takes an address of an ERC20 contract as parameter:

    ```act
    transition foo(address<Token> token_addr)
    iff true
    storage
        erc_token := token_addr as Token
    ```
    The parameter `token_addr` has type `address<Token>`, which indicates that the address points to a deployed contract of type `Token` (e.g. in our example an ERC20 token).
    
     This special type exists to allow Act to reason about calls to this contract now called `erc_token`, which *lives* at address `token_addr` inside the transition body. Ensuring that the spec which includes this annotated address types is equivalent to the implementation which only uses regular addresses is still possible and discussed in the <span style="color:red">
 correctness section (paragraph on Input space equivalence).</span>)

    
*Note:* Not all types in Act are allowed everywhere. There is a distinction between **ABI types** and **Storage types**:
1. **ABI types** include **base types** and **annotated address types**. They are used for function parameters and return values.
2. **Storage types** include **base types**, **mapping types**, and **contract types**. They are
 used for storage.

That means in function parameters and return values, mapping types and contract types are not allowed. Whereas in storage, annotated address types are not allowed.
