# Behaviors as State Transitions

*KIM: specificity relation in updates*

**Goal of this section**

Explain how behaviours define **state transitions**, focusing on `transfer`.

## Behaviour Signatures
Each externally callable function is specified as a behaviour.
For example:

```act
behaviour transfer(uint256 value, address to)
iff CALLVALUE == 0
```

This declares:
- the function parameters
- the precondition for successful execution
If the precondition fails, the behaviour reverts and makes no state changes.

## Case Splits and Control Flow
Act uses `case` blocks to describe control flow explicitly.
In the ERC20 `transfer` behaviour, we distinguish two cases:

```act
case CALLER =/= to:
  ...

case CALLER == to:
  ...
```

This separation is necessary because Act updates are **non-sequential**: all updates refer to the pre-state. Writing the cases explicitly avoids ambiguity.


## Storage Updates Are Simultaneous
Consider the main transfer case:

```act
storage
  balanceOf := balanceOf[
    CALLER => balanceOf[CALLER] - value,
    to     => balanceOf[to]     + value
  ]
```

This does not mean “subtract, then add”.
Instead, it means:
“In the final state, `balanceOf(CALLER)` equals the old balance minus `value`, and `balanceOf(to)` equals the old balance plus `value`.”
All right-hand sides are evaluated in the **initial state**.
This design avoids accidental order-dependence and makes behaviours suitable for formal reasoning.