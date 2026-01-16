# Type-Checking

act's type-checking process ensures that specifications are both syntactically correct and semantically sound. It combines traditional static type-checking with semantic verification using SMT solvers. Type safety and soundness are proven in detail. <span style="color:green">  A full tech report will be available shortly. </span>

The type-checker implements the formal typing judgments defined in act's type system. It verifies that all expressions are well-typed according to typing rules which take storage declarations, interface parameters, and local bindings into account. 
 The type-checker proceeds systematically: it first type-checks each contract's constructor, memorizing the constructor's storage declarations, then type-checks each transition against the updated environment. This ensures type consistency across the entire specification and catches errors like type mismatches, undefined variables, and invalid operations before proceeding to the verification backends.

 Additionally, the type-checker performs **semantic checks using SMT solvers** to verify properties that go beyond static typing. These checks ensure logical soundness and completeness of specifications and include verifying that:

1) **arithmetic expressions** are within the required bounds of their types; 
2) **constructor preconditions** hold when they are called;
3) **case conditions** are exhaustive and non-overlapping.

## 1. Arithmetic Safety

act requires explicit `inRange` expressions to verify that arithmetic operations stay within the bounds of their declared types. An SMT solver is used to verify this property symbolically for all intermediate and final arithmetic evaluations.

**Why it matters?**

To formally verify smart contract specifications, it is crucial to ensure that arithmetic operations do not overflow or underflow their intended types.  In Solidity, for example, arithmetic operations are checked at runtime to prevent overflows and underflows, if one occurs, the transaction reverts.

In act, a constructor/transition "reverts" if and only if the preconditions fail. Therefore, for an act specification to type-check, all arithmetic operations that could potentially overflow or underflow must be guarded by `inRange` checks in the preconditions. 
<span style="color:red"> what if we want to compare it to unchecked languages/old solidity? </span>

**How it works:**

When you write `inRange(uint256, expression)` in a precondition, the type-checker generates an SMT query to verify that for all valid pre-states satisfying the preconditions, the `expression` will always fit within the specified type's range (e.g., 0 to 2^256 - 1 for `uint256`).

**Example:**

*(snippet from [erc20.act](https://github.com/argotorg/act/blob/main/tests/hevm/pass/multisource/erc20/erc20.act), transfer transition)*

```act
transition transfer(address to, uint256 value)
iff 
  inRange(uint256, balanceOf[CALLER] - value)
  CALLER != to ==> inRange(uint256, balanceOf[to] + value)

case CALLER != to:
  updates
    balanceOf := balanceOf[
                    CALLER => balanceOf[CALLER] - value,
                    to => balanceOf[to] + value]
```

The SMT solver verifies that given 
- `inRange(uint256, balanceOf[CALLER] - value)` and 
- `CALLER != to ==> inRange(uint256, balanceOf[to] + value)`

No arithmetic overflow or underflow occurs in any (sub-)expression anywhere in this transition.


**Failure behavior:**

If an `inRange` condition (as any other precondition) fails, the transition reverts and no storage updates occur. This aligns with Solidity's execution model and allows act to precisely characterize the contract's input space.

## 2. Constructor Precondition Verification

When a constructor is called to create a new contract instance (e.g., `Token(100)` in a storage update), act verifies that the constructor's preconditions are satisfied at the call site.

**Why this matters:**

Contract creation is a crucial operation. If a constructor's preconditions aren't met, creation fails and the entire transaction reverts, which would therefore not actually initialize/update storage as specified. Therefore act has to ensure **every constructor call in the specification is valid**, for the entire act spec to be well-typed. <span style="color:red"> @Anja: please double-check my wording here (well-types, valid etc) </span>

**How it works:**

The type-checker implements a semantic check to verify if the current state and environment satisfy the constructor's preconditions: For each constructor call (e.g. `AMM(t0,t1)`), the SMT solver verifies that given the current constraints (preconditions, case conditions and current state, in our example `t0`, `t1`) , the constructor's preconditions are entailed.

**Example:**

We revisit the constructor of an AMM contract.

*(snippet from [amm.act](https://github.com/argotorg/act/blob/main/tests/hevm/pass/multisource/amm/amm.act))*

```act
contract Amm

constructor(address<Token> t0, address<Token> t1)
iff    t0 != t1
creates
    Token token0 := t0
    Token token1 := t1
...
```

When `Amm`'s constructor is called, e.g., in another contract's constructor:

```act
contract Wrapper
constructor(address<Token> t0, address<Token> t1)
iff true
creates
    Amm amm := Amm(t0, t1)
```

For the constructor call `Amm(t0, t1)`, the SMT solver verifies that given the current information: 

- preconditions: `true`,
- case conditions: none 
- information about the values `t0`, `t1`: they are of type `address<Token>`

the constructor precondition `t0 != t1` holds. In this example, this is clearly not the case, since `t0` and `t1` could be equal addresses. Therefore, this semantic check and would fail and therefore the  act specification does not type-check.  <span style="color:red"> What do we actually report if one of these checks fail? </span>

To fix the example, add the precondition `t0 != t1` to the `Wrapper` constructor.   

## 3. Case Condition Verification

The last semantic check happening during type-checking is about the `case` conditions in transitions and constructors. As explained before, act
 uses `case` blocks to represent different execution paths in constructors and transitions. In this check, the SMT solver verifies two critical properties of case conditions:

**a) Exhaustiveness**: The case conditions must cover all possible scenarios given the preconditions. Formally, the type system requires:

```
preconditions ==> (C₁ or C₂ or ... or Cₙ)
```
where `Cᵢ` are the case conditions.

**b) Non-overlapping**: The case conditions must be mutually exclusive. For any two distinct cases i and j, their conditions cannot both be true at the same time:

```
not (Cᵢ and Cⱼ)
```

**Why this matters:**

If one of this two properties does not hold, the specification is ambiguous or incomplete and therefore unsound: If the case conditions are not exhaustive, there exist inputs for which no case applies, leading to undefined behavior. Similarly, if case conditions overlap, multiple cases apply simultaneously, causing ambiguity in the contract's behavior.

**Example**

We revisit the transfer transition of the ERC20 contract: 

*(snippet from [erc20.act](https://github.com/argotorg/act/blob/main/tests/hevm/pass/multisource/erc20/erc20.act), transfer transition)*

```act
transition example(address to, uint256 value) : bool
iff
    inRange(uint256, balanceOf[CALLER] - value)
    CALLER != to ==> inRange(uint256, balanceOf[to] + value)

case CALLER != to:
  storage
    balanceOf := balanceOf[
                    CALLER => balanceOf[CALLER] - value,
                     to    => balanceOf[to] + value ]
    returns true

case CALLER == to:
    returns true
```

✓ The SMT solver verifies:
- **Exhaustive**: `(CALLER == to) or (CALLER != to)` is always true
- **Non-overlapping**: `(CALLER == to) and (CALLER != to)` is always false


