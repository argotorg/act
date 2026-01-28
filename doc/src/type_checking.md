# Type-Checking

act's type-checking process ensures that specifications are both syntactically correct and semantically sound. It combines traditional static type-checking with semantic verification using SMT solvers. Type safety is proven in detail. <span style="color:green">  A full tech report will be available shortly. </span>

The type-checker implements the formal typing judgments defined in act's type system. It verifies that all expressions are well-typed according to typing rules, which take storage declarations, interface parameters, and local bindings into account. 
 The type-checker proceeds systematically: it first type-checks each contract's constructor, memorizing the constructor's storage declarations, then type-checks each transition against the updated environment. This ensures type consistency across the entire specification and catches errors like type mismatches, undefined variables, and invalid operations before proceeding to the verification backends.

 Additionally, the type-checker performs **semantic checks using SMT solvers** to verify properties that go beyond static typing. These checks ensure logical soundness and completeness of specifications and include verifying that:

1) **arithmetic expressions** are within the required bounds of their types; 
2) **constructor preconditions** hold when they are called;
3) **case conditions** are exhaustive and non-overlapping.

## 1. Arithmetic Safety

act requires explicit `inRange` expressions to verify that arithmetic operations stay within the bounds of their declared types. An SMT solver is used to verify this property symbolically for all intermediate and final arithmetic evaluations.

**Why it matters?**

To formally verify smart contract specifications, it is crucial to ensure that arithmetic operations do not overflow or underflow their intended types.  In Solidity, for example, arithmetic operations are checked at runtime to prevent overflows and underflows, if one occurs, the transaction reverts.

In act, a constructor/transition "reverts" if and only if the preconditions fail. Therefore, for an act specification to type-check, all arithmetic operations that could potentially overflow or underflow in the compiled bytecode must be guarded by `inRange` checks in the preconditions. 
(Note that if the contract code does not check for overflow, then act should not check for it either.)
If the act spec does not express the possibility of overflow anywhere, then there will be no overflow (assuming the contract's behaviour is also [proven equivalent](./equiv.md)). 


**How it works:**

When you write `inRange(uint256, expression)` in a precondition, the type-checker generates an SMT query to verify that for all valid pre-states satisfying the preconditions (one of them being the `inRange` condition itself), no expression in the constructor/transition can evaluate to a value that falls outside the specified type's range (e.g., 0 to 2^256 - 1 for `uint256`).

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

### Technical Background

The reason for not only checking the **top-level expressions** but also all **intermediate expressions** comes from act's equivalence checker, which is imported from hevm (see [hevm backend: Equivalence to EVM bytecode](./equiv.md)).
 The equivalence checker uses hevm's internal representation, which does not have unbounded integers, and therefore all expressions must be representable in the EVM's 256-bit integer space.

 *Note: it is suggested to read section [hevm backend: Equivalence to EVM bytecode](./equiv.md) before continuing.*

 **EVM semantics vs. act semantics**

The semantics of the EVM (and subsequently hevm) and act are slightly different when it comes to overflow. 
The former has modulo arithmetic while the latter has unbounded integers.
So, for example, in the case of multiplication,
-  the semantics of the EVM opcode is:
   `MUL opA opB = (opA * opB) % 256`, where * is the mathematical operation of multiplication
-  whereas in act, the semantics are the actual mathematical ones.

**Relevance for Equivalence Checking**

Let's see how this difference leads to requiring overflow checks for intermediate expressions.
Assume we want to **check the equivalence** of the following Solidity function with the following act transition: 

*Solidity function `f`*

```Solidity
contract A {
  uint256 a; uint256 b;

  function f(uint256 x) returns(uint256) {
    require(COND, "some desired precondition");
    a = x;
  }
}
```

*act transition `f`*

```act
contract A
  ...
  transition f(uint256 x) : uint256
  iff
    COND // the same as the solidity code

  updates
    a := x*b/b
```

In this example both formulations have identical preconditions. In other words the [input space is equivalent](./equiv.md#input-space-equivalence), and will be demonstrated to be so by hevm.

Therefore let us study the **storage updates**:

On the one side the final value of the storage variable `a` is `x`, while on the other it is `x*b/b`, where the operators follow act's semantics. Since act's semantics are those of **unbounded integers**, the spec is **equivalent** for this transition, and we would want the equivalence checker to confirm this.

However, since act's equivalence checker is imported from hevm, using its Expr representation, which does not have unbounded integers, this will fail:
 It is not possible to translate act's pure, unbounded `*` and `/` to hevm's `MUL` and keep the same semantics, because 
 - while in act `b` may be any number in `uint256` (and does not need to appear in the preconditions since `x*b/b` it will simplify to `x` for any non-zero `b`), 
 - there will always be value of `b`  in `uint256`  sufficiently large to cause `x*b` overflow out of the 256-bit range. And this leads to the the equivalence checker concluding that `x == x*b/b` is false.

To address this, act implements its **additional overflow pass**. It checks that given the preconditions, all the **intermediate expressions** have values within the range representable by hevm. Note that it checks this on the act level, i.e. using SMT passes on unbounded integer theory. This guarantees that we operate under an input space in which the semantics of act's `*` and the EVM's `MUL` opcode are identical. So in the above example, it will return an error that says that the specification cannot be equivalence checked because it contains expressions that are not computable by the EVM.
<!-- The idea is not that you will add a precondition to cover this (as that would lead to a mismatch in the input space, if the new one is not present in the bytecode as well), but that you will have to express things in a computable way. -->

This is not really a limitation on the number of contract's we can specify, as any realizable contract's behaviour must be expressible through computable expressions.


This **output error** for the above example looks as follows:




```sh
Operands of / must be both signed or both unsigned
counterexample:

  calldata:

    (x = 2)

  environment:

    CALLVALUE = 0

  storage:
    
    prestate:

      x = 2
      pre(b) = 57896044618658097711785492504343953926634992332820282019728792003956564819968


:
9 |       a := x*b/b
                  ^
Result of * must be in the range of int256 or uint256
counterexample:

  calldata:

    (x = 2)

  environment:

    CALLVALUE = 0

  storage:
    
    prestate:

      x = 2
      pre(b) = 57896044618658097711785492504343953926634992332820282019728792003956564819968


:
9 |       a := x*b/b
                ^
Integer expression of type integer is not guaranteed to fit in type uint256
counterexample:

  calldata:

    (x = 0)

  environment:

    CALLVALUE = 0

  storage:
    
    prestate:

      x = 0
      pre(b) = 0


:
9 |       a := x*b/b
                  ^
```


**Expressing Overflow/Underflow in act**

To express overflow/underflow in act, the ideal way would be to write `(a+b)%n`, which is what overflow is mathematically. This works for all ranges, except the 256-bit one, where the additional overflow pass will catch `a+b`. There is currently no way to express 256-bit-overflow in act without triggering the overflow pass.

<!-- So what would need is something like primitives, i.e. addOverflow(a,b), which in act semantics will be the same thing, but will not trip up the overflow pass. Or maybe a simple informed filtering would do, to allow (a op b)%n to pass the overflow checker direclty since we know we can actually translate it. -->

## 2. Constructor Precondition Verification

When a constructor is called to create a new contract instance (e.g., `new Token(100)` in a storage update), act verifies that the constructor's preconditions are satisfied at the call site.

**Why this matters:**

Contract creation is a crucial operation. If a constructor's preconditions aren't met, creation fails and the entire transaction reverts, which would therefore not actually initialize/update storage as specified. Therefore act has to ensure **every constructor call in the specification is valid**, for the entire act spec to be well-typed. 

**How it works:**

The type-checker implements a semantic check to verify if the current state and environment satisfy the constructor's preconditions: For each constructor call (e.g. `AMM(t0,t1)`), the SMT solver verifies that given the current constraints (preconditions, case conditions and current state, in our example `t0`, `t1`) , the constructor's preconditions are entailed.

**Example:**

We revisit the constructor of an AMM contract.

*(snippet from [amm.act](https://github.com/argotorg/act/blob/main/tests/hevm/pass/multisource/amm/amm.act))*

```act
contract Amm

constructor(address<Token> t0, address<Token> t1)
iff   address(t0) != address(t1)
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
    Amm amm := new Amm(t0, t1)
```

For the constructor call `Amm(t0, t1)`, the SMT solver verifies that given the current information: 

- preconditions: `true`,
- case conditions: none 
- information about the values `t0`, `t1`: they are of type `address<Token>`

the constructor precondition `address(t0) != address(t1)` holds. In this example, this is clearly not the case, since `t0` and `t1` could be equal addresses. Therefore, this semantic check would fail and therefore the  act specification does not type-check, reporting an error 
```sh
Preconditions of constructor call to "Amm" are not guaranteed to hold
``` 
and listing a counterexample calldata.

To fix the example, add the precondition `address(t0) != address(t1)` to the `Wrapper` constructor.   

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
transition transfer(address to, uint256 value) : bool
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


