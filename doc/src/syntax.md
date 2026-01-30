# Syntax of the Act language

A specification of one or more contracts written in `act` consists of a `contract` block for each contract, which in turn contains a single
`constructor` and a set of `transitions`.

The `constructor` specification defines the structure of the contract
state, the initial value for the state, and the conditions under which
the contract can be created.

Each `transition` specification determines how a contract function updates
the state, its return value, and the conditions that must be
satisfied in order for it to be applied.

Alternatively, they can be thought of an initial state and a
set of state transitions, determining an inductively defined
state transition system.

The specifications can be exported to different backends in order to
prove that the claims that are being made hold with respect to an implementation.

## Basic Elements

- **Types**:

   in act there are three kinds of types: simple ABI types (e.g., `uint256`, `address`, `bool`), mapping types (e.g., `mapping(address => uint256)`), and contract types (e.g., `Token`). 
  These types are explained in detail in [Types](./store_type.md#types).
- **Expressions**:

    expressions in act are used to initialize storage variables, describe state updates and to express conditions. 
   They can be simple variables, constants, arithmetic expressions, or more complex expressions such as mapping lookups. 
  Expressions are explained in detail in [Expressions](./store_type.md#expressions).
- **Storage**:

    The storage is the key element of a contract's state. 
  It is declared and initialized in the `creates` block of the constructor. 
  Storage updates are specified in the `updates` block of transitions. 
  Storage is explained in detail in [Storage](./store_type.md#storage).
- **Constructor**: 

   The constructor defines the initial state of the contract and the conditions for its creation. 
  Constructors are explained in detail in [Constructors and Initial State](./constructors.md).
- **Transitions**:

    Transitions define how the contract state changes in response to function calls. 
  They specify preconditions for the function calls and the resulting state updates. 
  Transitions are explained in detail in [Transitions and Storage Updates](./transitions.md).

A tutorial on how to write your own act specification can be found in [How to Write Your Own Spec](./how_to.md).
