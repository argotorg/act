# How to Write Your Own Spec

**Table of Contents**

- [Overview: From implementation to act](#overview-from-implementation-to-act)
- [Step 1: Understand the Contract Structure](#step-1-understand-the-contract-structure)
- [Step 2: Establish Preconditions](#step-2-establish-preconditions)
- [Step 3: Define the `case` Blocks](#step-3-define-the-case-blocks)
- [Step 4: Initialize Storage in the Constructor](#step-4-initialize-storage-in-the-constructor)
- [Step 5: Specify Storage Updates and Return Values](#step-5-specify-storage-updates-and-return-values)
  - [Storage Updates](#storage-updates)
  - [Return values](#return-values)
- [Summary](#summary)
- [Inline Function Calls](#inline-function-calls)
  - [Why Inlining is Required](#why-inlining-is-required)
  - [How to Inline Function Calls](#how-to-inline-function-calls)
  - [Example: Simple Function Call](#example-simple-function-call)
  - [Example: Function Call with Branching](#example-function-call-with-branching)
  - [Special Note: Constructor Calls](#special-note-constructor-calls)

---

This section provides a step-by-step guide on writing your own act specification for an Ethereum smart contract. We will cover the essential components, best practices, and common patterns to help you get started quickly.

<!--  
- inrange - > for every arithmetic operation that can overflow or underflow, add - an inrange check before it. See Arithmetic Safety for more details.
- transitions -> also getter functions have to be considered
- require -> precondition
- inline function calls
- overview of from general to specific in updates
- initialize balance? -->

## Overview: From implementation to act

For the purposes of this tutorial, we will refer to Solidity implementation, but the concepts apply equally to other Ethereum contract languages.

The general process of writing an act specification involves: 

1. **Understand the Contract Structure**: Identify contract name, constructor parameters, public state variables (storage), and all external/public functions (transitions including getters).
2. **Establish Preconditions**: Convert Solidity's `require` statements to act's `iff` preconditions and add `inRange` checks for arithmetic safety to prevent overflow/underflow.
3. **Define the `case` Blocks**: Use `case` blocks to handle different execution paths (from if-then-else, mapping updates with overlapping keys, or inlined function calls).
4. **Initialize Storage in the Constructor**: Initialize all storage variables with their initial values in the `creates` block.
5. **Specify Storage Updates and Return Values**: List all storage updates in the `updates` block (remembering they are simultaneous) and specify return values for functions with return types.

We will use a running example, that was introduced in [Storage Updates are Partially Ordered](./transitions.md#storage-updates-are-partially-ordered), to illustrate the steps. Imagine we have the follwing solidity code declaring two contracts, which we want to specify in act:

*(code from [ordered_updates.sol](https://github.com/argotorg/act/blob/main/tests/hevm/pass/ordered_updates/ordered_updates.sol) <span style=color:red> double check link </span>)*

```solidity
pragma solidity >=0.8.0;

contract Admins {
    address public admin1;
    address public admin2;

    constructor(address _admin1) {
        admin1 = _admin1;
        admin2 = tx.origin;
    }

    function set_admin2(address new_admin2) public {
        admin2 = new_admin2;
    }

}

contract Asset {
    uint256 public value;
    Admins admins;
    mapping (address => uint256) public balanceOf;

    constructor(uint256 _value) {
        value = _value;
        admins = Admins(msg.sender);
        balanceOf[address(this)] = _value;
    }

    function assetTransfer(uint256 amt, address to) public returns (bool) {
        require (msg.sender == admins.admin1() || msg.sender == admins.admin2());

        balanceOf[address(this)] = balanceOf[address(this)] - amt;
        balanceOf[to] = balanceOf[to] + amt;

        return true;
    }

    function setAdmins(address new_admin1, address new_admin2) public {
        if (msg.sender == admins.admin1() || msg.sender == admins.admin2()) {
            admins = Admins(new_admin1);
            admins.set_admin2(new_admin2);
        }
    }
}
```

## Step 1: Understand the Contract Structure

Begin by analyzing your Solidity contract:
- Identify the **contract name** and specify it in act using the `contract` keyword.
- Specify the **constructor**: Look for the constructor function and note its parameters. Specify it using the `constructor` keyword and copy the constructor parameters. If the parameter is `address` and is later cast to a contract type `<ContractName>`, use an annotated contract type `address<ContractName>`. If the constructor is payable in the source code, mark it as `payable` in act (`constructor payable(<parameters>)`). Leave the `iff` blank for now.
- Identify all **public state variables**. These become storage in act and will be initialized in the constructor. In solidity they are listed at the top of the contract. List them in the constructor's `creates` block: Specify the **type** and **name** of each storage variable.
- List all **external and public functions**. These become transitions. Also the getter functions for public state variables which are automatically generated by Solidity have to be listed as transitions. You have to name these getter functions the same as corresponding storage variables. Specify the transitions after the constructor using the `transition` keyword (respectively `transition payable` for payable ones), copy the parameters from the source code. If the parameter is `address` and is later cast to a contract type `<ContractName>`, use an annotated contract type `address<ContractName>`. If a function has a return value, specify its type after the parameter list using `: <return_type>`.

What we would have at this point for our example:

```act
contract Admins
 
constructor(address _admin1)
iff <todo>

creates
    address admin1 := <todo>
    address admin2 := <todo>

transition set_admin2(address new_admin2)
<todo>

transition admin1() : address
<todo>

transition admin2() : address
<todo>


contract Asset

constructor(uint256 _value)
iff <todo>
creates
    uint256 value := <todo>
    Admins admins := <todo>
    mapping(address => uint256) balanceOf := <todo>

transition assetTransfer(uint256 amt, address to)
<todo>

transition setAdmins(address new_admin1, address new_admin2)
<todo>

transition value() : uint256
<todo>

transition balanceOf(address account) : uint256
<todo>
```



## Step 2: Establish Preconditions

The preconditions of a transition are specified in the `iff` block. They define the conditions that must hold for the transition to execute successfully. It combines explicit and implicit requirements:
- **Explicit requirements**: These are conditions that are explicitly checked in the Solidity code using `require` statements. Each `require` statement translates to a line in the `iff` block.
Some preconditions arise from the unique ownership requirement, i.e. storage of the contract does not contain any aliased reference to another contract, see [aliasing](./aliasing.md) section. This would usually mean that if many contract addresses are taken as parameters to constructors or transitions, the ones stored in the storage have to be distinct. Note that these 
need to already be present in the Solidity implementation of the contract, not merely in the act specification.
- **Implicit requirements**: These are conditions that are not explicitly listed in the code but are necessary for the correct execution of the transition: These are checks to prevent arithmetic overflow/underflow.  Arithmetic safety is addressed using the `inRange` expression. To ensure every arithmetic operation is safe, an `inRange` check has to be added for every occurring operation. 

**Guidelines:**
- Convert each `require(condition)` to a line in the `iff` block
- Multiple conditions are implicitly conjunctive (all must be true)
- Each arithmetic operation that can overflow/underflow must have a corresponding `inRange` check (Syntax `inRange(<type>, <expression>)`)
- Use logical operators (`and`, `or`, `==>` (implication), etc.) as needed. Full list of operators can be found in [Base Expressions](./store_type.md#base-expressions)
- The syntax to access fields of a mapping is `mapping_name[key]`.
- When accessing fields of other contracts, use dot notation: `contract_instance.field_name`
- Use the special variables to describe EVM environment:
    - `CALLER` instead of `msg.sender`
    - `CALLVALUE` for the amount of Ether sent
    - `THIS` for the contract's own address
    - `ORIGIN` for `tx.origin`



Our example specification would look like this after adding the preconditions. In practice one would fill on transition at a time. But for clarity we follow each step for the whole spec.:

```act
contract Admins
 
constructor(address _admin1)
iff true

creates
    address admin1 := <todo>
    address admin2 := <todo>

transition set_admin2(address new_admin2)
iff true
<todo>

transition admin1() : address
iff true
<todo>

transition admin2() : address
iff true
<todo>

contract Asset

constructor(uint256 _value)
iff true
creates
    uint256 value := <todo>
    Admins admins := <todo>
    mapping(address => uint256) balanceOf := <todo>

transition assetTransfer(uint256 amt, address to)
iff CALLER == admins.admin1 or CALLER == admins.admin2
    inRange(uint256, balanceOf[THIS] - amt)
    THIS != to ==> inRange(uint256, balanceOf[to] + amt)
<todo>

transition setAdmins(address new_admin1, address new_admin2)
iff true
<todo>

transition value() : uint256
iff true
<todo>

transition balanceOf(address account) : uint256
iff true
<todo>
```
The only interesting precondition is in the `assetTransfer` transition, which corresponds to the `require` statement in the Solidity code and two `inRange` checks. The other transitions have trivial preconditions (`iff true`).
Let us look closer into the `inRange` checks:
- In the Solidity function `assetTransfer`, the line `balanceOf[address(this)] = balanceOf[address(this)] - amt;` performs a subtraction. To ensure that this subtraction does not underflow, we add the precondition `inRange(uint256, balanceOf[THIS] - amt)`.
- If the previous line did not revert, the code proceeds to the line `balanceOf[to] = balanceOf[to] + amt;`, where it performs an addition. If `to` is different from `this`, this addition could overflow, otherwise (if `to == this`) it will just go back to its original value.
To ensure that this addition does not overflow, we add the precondition `THIS != to ==> inRange(uint256, balanceOf[to] + amt)`.


## Step 3: Define the `case` Blocks

If the constructor or a transition has multiple paths either explicit, through e.g. an `if then else` or implicit where the transition's behavior changes depending on something (e.g. whether `THIS == to` in the step above), `case` blocks have to be used to separate these paths. Each `case` block has a condition and the corresponding storage initialization or updates.

To paraphrase, within each `case` block the what happens to the storage of the contract can be defined through the same set of equations that hold after the execution of the function in this particular case. This set of equations is defined in the `creates` block for constructors and in the `updates` block for transitions.

When there is just one single path in a constructor or transition, no `case` block is needed. Proceed to step 4 in this case.

**Common Patterns for `case` Blocks**
- **If-then-else**: When there are two or more paths (e.g., an `if-else`), use `case` blocks with complementary conditions.
- **Changing Values of Mappings**: When two or more keys of a mapping are assigned new values, the end state of the mapping depend on if some of the keys were equal or not. Use `case` blocks to separate these scenarios.
-  **Function Calls**: As mentioned before: act describes the impact a function has on a contract's storage. Hence, if within a Solidity function, another function is called, this has to be **"inlined"** in the act specification. That means the called function's logic has to be flattened into the current one's. Which most likely leads to `case` blocks. Details below in section [Inline Function Calls](how_to.md#inline-function-calls). Note that this **only** applies to transitions, constructors **can** in fact be called in act without inlining. 


**Guidelines:**
- Conditions of the `case` blocks must be mutually exclusive and exhaustive
- Multiple conditions are implicitly conjunctive (all must be true)
- Use logical operators (`and`, `or`, `==>` (implication), `==`, `!=`, etc.) as needed. Full list of operators can be found in [Base Expressions](./store_type.md#base-expressions)
- The syntax to access fields of a mapping is `mapping_name[key]`.
- When accessing fields of other contracts, use dot notation: `contract_instance.field_name`
- Use the special variables to describe EVM environment:
    - `CALLER` instead of `msg.sender`
    - `CALLVALUE` for the amount of Ether sent
    - `THIS` for the contract's own address
    - `ORIGIN` for `tx.origin`


After considering this step the specification of the running example only the transiitons `assetTransfer` and `setAdmins` changed, since all other transitions and constructors hve only one path. The transitions with `case` blocks look like this:

```act

transition assetTransfer(uint256 amt, address to)
iff CALLER == admins.admin1 or CALLER == admins.admin2
    inRange(uint256, balanceOf[THIS] - amt)
    THIS != to ==> inRange(uint256, balanceOf[to] + amt)

case THIS != to
<todo>

case THIS == to
<todo>



transition setAdmins(address new_admin1, address new_admin2)
iff true

case  CALLER == admins.admin1 or CALLER == admins.admin2
<todo>

case not (CALLER == admins.admin1 or CALLER == admins.admin2)
<todo>

```

In the `assetTransfer` function, the values of `THIS` and `to` of the `balanceOf` mapping are changed. Which equations are true afterwards depend on whether `THIS` and `to` are identical.

In `setAdmins`, there is a simple `if` that splits two paths, hence also in the act spec we have two paths accordingly.


## Step 4: Initialize Storage in the Constructor

The constructor initializes all storage variables. Every storage variable must be initialized in every execution path (i.e. in every `case` block).
This has been mostly prepared already in step 1.
What is left to do is 
- copy the behavior of Solidity's constructors while considering the following guidelines 
- and for **payable** constructors: the contracts balance in Ether has to be initialized. This is done using the special variable `BALANCE` with type `uint256`:

    Most of the time this is just `uint256 BALANCE := CALLVALUE`, but if there are more complex behaviors in the Solidity constructor, such as forwarding some of the `CALLVALUE` to another contract's constructor, this has to be reflected here (e.g. `uint256BALANCE := CALLVALUE - <forwardedAmount>`).
- ensure that no two storage instances refer to the same contract (unique ownership invariant, see [Aliasing](./aliasing.md) section). This already has to hold in the Solidity implementation.

**Guidelines:**
- Use `:=` to assign the initial value
- For `payable` constructors, initialize the contract's balance in Ether using the special variable `BALANCE`
- For mappings, use `[]` for empty mappings or `[<key> => <value>, ...]` to initialize specific entries. Entries that are not specified are set to the type's default value.
- In every `case` block  **all** storage variables must be initialized.
- As in Solidity, **constructors** of other contracts can be called and assigned using the keyword `new`.
- Use the special variables to describe EVM environment:
    - `CALLER` instead of `msg.sender`
    - `CALLVALUE` for the amount of Ether sent
    - `THIS` for the contract's own address
    - `ORIGIN` for `tx.origin`
    - `BALANCE` for the contract's balance in Ether


In our example the constructors of the two contracts have this final form:

```act
contract Admins

constructor(address _admin1)
iff true

creates
   address admin1 := _admin1
   address admin2 := ORIGIN

...

contract Asset

constructor(uint256 _value)
iff true
creates
    uint256 value := _value
    Admins admins := new Admins(CALLER)
    mapping(address => uint256) balanceOf := [THIS => _value]
```



## Step 5: Specify Storage Updates and Return Values

What is left to do now, is to explicitly list all storage slots that were updated in each transition and each `case` block. As well as specify the return value if there is a return type in the transition signature. 
We start with the **storage updates**. 

### Storage Updates

If for a transition and `case` no storage slot was changed, then the `updates` block is skipped. A common example for such a case are getter functions.

For all other transitions and `case` blocks, there has to be an `updates` block. The updated storage slots are listed after the keyword; one update per line.
The syntax to update a storage slot is `<storage_slot> := <new_value>`. 

Be aware that **Storage updates are simultaneous!** That means that all right-hand sides of the updates are evaluated in the pre-state (before the function call). This avoids order-dependence and makes transitions suitable for formal reasoning. As mentioned before,
these update statements serve as a set of equations that hold after execution. They are not to be seen as assignments. 

Consequently, every storage slot can be mentioned within the same `case` block at most once (except for the *special case* explained below).  Further, mappings are updated as a whole in one single statement, not one update per mapping entry. 

If the **contract's balance** in Ether changes during its execution (e.g. by calling a payable constructor), this has to be reflected in the `updates` block by updating the special variable `BALANCE` accordingly.

There is one  **special case** about updates. If a contract uses an instance of another contract in its storage, as the `Asset` contract contains an instance of the `Admins` contract in our example, which is called `admins`; and if now, within one transition and `case` block, the entire `admins` contract instance is updated and also one of `admins`'  fields is updated, the more general update has to be stated before the more specific one. For details see [Storage Updates Ordering](./transitions.md#storage-updates-are-partially-ordered).

**Guidelines:**
- The syntax for updating a mapping is : `mapping_name := mapping_name[key1 => new_value1, key2 => new_value2]`
- All right-hand sides use **pre-state values** (e.g., `balanceOf[CALLER] - value` subtracts from the old balance)
- Right-hand-sides of updates **cannot** be transition calls. Transition calls have to be inlined as described in step 3 and section [Inline Function Calls](#inline-function-calls)
- If the contract's balance in Ether changes, update it using the special variable `BALANCE`
- Every storage slot can be mentioned at most once per `case` block, except for the explained special case
- Consider the special case: state more general updates before more specific ones
- Ensure that no two storage instances refer to the same contract (unique ownership invariant, see [Aliasing](./aliasing.md) section).

### Return values

For each transition where the signature specifies a return type,  `returns <expr>` has to be present for each `case` block. The returned expression can reference storage and parameters but always refers to the pre-state.

**Guidelines:**
- Use `returns expression` to specify the return value
- The return value can reference storage and parameters but always refers to the pre-state


The final act specification of the Solidity code at the beginning of this page is the following:

*(also available as [ordered_updates.act](https://github.com/argotorg/act/blob/main/tests/hevm/pass/ordered_updates/ordered_updates.act) <span style= color:red> double check link </span>)*

```act
contract Admins

constructor(address _admin1)
iff true

creates
   address admin1 := _admin1
   address admin2 := ORIGIN

transition set_admin2(address new_admin2)
iff true
updates
   admin2 := new_admin2

transition admin1() : address
iff true
returns admin1

transition admin2() : address
iff true
returns admin2





contract Asset

constructor(uint256 _value)
iff true
creates
    uint256 value := _value
    Admins admins := Admins(CALLER)
    mapping(address => uint256) balanceOf := [THIS => _value]


transition assetTransfer(uint256 amt, address to) 

iff CALLER == admins.admin1 or CALLER == admins.admin2
    inRange(uint256, balanceOf[THIS] - amt)
    THIS != to ==> inRange(uint256, balanceOf[to] + amt)

case THIS != to

updates
   balanceOf := balanceOf[
                  THIS => balanceOf[THIS] - amt,
                  to   => balanceOf[to]   + amt ]

case THIS == to



transition setAdmins(address new_admin1, address new_admin2)

iff true

case CALLER == admins.admin1 or CALLER == admins.admin2

updates
   admins := new Admins(new_admin1)
   admins.admin2 := new_admin2

case not (CALLER == admins.admin1 or CALLER == admins.admin2)


transition value() : uint256
iff true
returns value

transition balanceOf(address idx) : uint256
iff true
returns balanceOf[idx]

```

Note that in `setAdmins`, we are in this special case where a contract instance and one of its fields are updated in the same `updates` block. So the general update of `admins` comes first, and the update of `admins.admin2` comes second.


## Summary

1. **Be explicit about control flow**: Use `case` blocks liberally to avoid ambiguity
2. **Use annotated address type**: If an address is used as a contract instance in the source code, annotate it with the contract type (e.g., `address<ContractName>`).
3. **Check arithmetic safety**: Use `inRange` for every operation that could overflow/underflow and add it to `iff`
4. **Remember updates are simultaneous**: All right-hand sides refer to the pre-state
5. **Initialize all storage variables**: Every storage variable must appear in every `creates` block (in the constructor).
6. **Make conditions exhaustive**: Each set of cases must cover all possibilities
7. **Convert all requirements**: Every Solidity `require` becomes an `iff` condition or implicit in a case
8. **Specify getters**: Even view functions need to be specified as transitions using the same name as storage variables.
9. **Use meaningful variable names**: Match your Solidity code for clarity
10. **Inline transition calls**: A storage update cannot be a transition call, it's logic and affects have to be embedded as case blocks.
11. **Be aware of ordered updates**: When storage updates a contract instance and a field of that contract instance, the contract instance itslef has to be listed first in the `updates` block
12. **Reference the documentation**: Consult the [Storage, Typing and Expressions](./store_type.md), [Constructors](./constructors.md), and [Transitions](./transitions.md) sections for detailed explanations






## Inline Function Calls

When a function of a smart contract calls another function and uses its return value to update storage, act requires you to **inline** the called function's behavior (in the transition) rather than representing it as a function call. This design choice is crucial for formal reasoning: it makes the complete state transition explicit and avoids the need to reason about nested function calls.

### Why Inlining is Required

In act, storage updates must be explicit expressions that can be evaluated in the pre-state. Function calls are not allowed on the right-hand side of storage updates because:

1. **Formal reasoning**: act specifications describe state transitions as mathematical equations. Inlining makes these equations self-contained and verifiable.
2. **Clarity**: The complete behavior of each transition is visible in one place, without needing to trace through multiple function definitions.
3. **Composability**: Each transition can be analyzed independently without worrying about side effects from nested calls.

### How to Inline Function Calls

When you encounter a Solidity function that calls another function, follow these steps:

1. **Identify the called function**: Note what function is being called and what it does.
2. **Expand the call**: Replace the function call with the logic of the called function.
3. **Add cases if needed**: If the called function has multiple execution paths (cases), these must be reflected in the "calling" transition's cases.
4. **Combine preconditions**: The preconditions of the called function have to be considered in the calling transition. Possibly, by adding them as implications (`<case condition where call occurs> ==> <called transition's precondition>`) to the preconditions.

### Example: Simple Function Call

Consider this Solidity code where `updateBalance` calls `computeNewBalance`:

```solidity
contract Example {
    uint256 public balance;
    
    function computeNewBalance(uint256 amount) internal view returns (uint256) {
        return balance + amount;
    }
    
    function updateBalance(uint256 amount) public {
        balance = computeNewBalance(amount);
    }
}
```

**Incorrect act specification** (function call in update):
```act
// This is NOT valid act syntax
transition updateBalance(uint256 amount)
iff true
updates
   balance := computeNewBalance(amount)  // ❌ Function calls not allowed here
```

**Correct act specification** (inlined):
```act
transition updateBalance(uint256 amount)
iff inRange(uint256, balance + amount) // ✓ Added the (implicit) precondition of computeNewBalance
updates
   balance := balance + amount  // ✓ Inlined the logic of computeNewBalance
```

### Example: Function Call with Branching

Extending the previous example, consider what happens when the called function has multiple paths:

```solidity
contract BranchingExample {
    uint256 public balance;
    
    function computeNewBalance(uint256 amount, bool addBonus) internal view returns (uint256) {
        if (addBonus) {
            return balance + amount + 1;
        } else {
            return balance + amount;
        }
    }
    
    function updateBalance(uint256 amount, bool addBonus) public {
        balance = computeNewBalance(amount, addBonus);
    }
}
```

**Incorrect act specification**:
```act
// This is NOT valid act syntax
transition updateBalance(uint256 amount, bool addBonus)
iff true
updates
   balance := computeNewBalance(amount, addBonus)  // ❌ Function call
```

**Correct act specification** (inlined with cases and preconditions):
```act
transition updateBalance(uint256 amount, bool addBonus)
iff addBonus ==> inRange(uint256, balance + amount + 1)
    (not addBonus) ==> inRange(uint256, balance + amount)

case addBonus
updates
   balance := balance + amount + 1  // ✓ Inlined the bonus case

case not addBonus
updates
   balance := balance + amount  // ✓ Inlined the no-bonus case
```

Note how:
- The branching logic from `computeNewBalance` becomes case conditions
- The arithmetic safety check (`inRange`) is added to the preconditions using implications
- Each case explicitly states what value `balance` takes after the transition



### Special Note: Constructor Calls

Unlike transition calls, **constructor calls do not need to be inlined**. You can write:

```act
creates
   Admins admins := Admins(new_admin1)  // ✓ Constructor call is allowed
```

This is because constructors create new contract instances rather than modifying existing state, making them fundamentally different from transition calls in terms of formal reasoning.



