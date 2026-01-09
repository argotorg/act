# Aliasing and Unique Ownership

In order to reason about smart contracts in a purely functional way, we leverage the concept of **unique ownership**. This means that each contract has a single owner, and there are no shared references to the contract's state. This simplifies reasoning about state changes and ensures that contracts cannot inadvertently interfere with each other.

We showcase an issue with aliasing in the following example: suppose we have a contract A that contains two storage variables that contain an ERC20 token: `Token t0` and `Token t1`.

```act
contract A 
    constructor(address<Token> a0, address<Token> a1) 
        creates 
            Token t0 := a0
            Token t1 := a1
    transition transfer (uint256 value, address to)
        updates 
            t0.balanceOf := t0.balanceOf[CALLER => t0.balanceOf[CALLER] - value]
            t1.balanceOf := t1.balanceOf[to => t1.balanceOf[to] + value]

```

To reason about the contract A in Rocq in a purely functional way, we would map the contract to a Rocq record of type 
```rocq
Record State := {t0: Token.State; t1: Token.State}
```
In this example, if `a0` and `a1` point to the same ERC20 `Token` contract, then the `transfer` transition update of `t0.balanceOf` will also affect `t1.balanceOf`, breaking the functional abstraction we want to achieve (namely modifying only the `t0` field in the record).
<!-- Maybe we can run act and show the error it reports? -->
<!-- We can also specify how this record will look like in the rocq output. -->
However, if we can prove that `t0` and `t1` can never alias then we can safely reason about their state changes independently. Note that including an `iff a0 != a1` condition in the constructor's preconditions is required, but not sufficient, as the `Token` contract itself also needs to preclude aliasing. 

This unique ownership property is verified automatically for Act specifications using symbolic execution and SMT solving.
