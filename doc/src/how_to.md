# How to Write Your Own Spec

This section provides a step-by-step guide on writing your own Act specification for an Ethereum smart contract. We will cover the essential components, best practices, and common patterns to help you get started quickly.

inrange - > for every arithmetic operation that can overflow or underflow, add an inrange check before it. See Arithmetic Safety for more details.
transitions -> also getter functions have to be considered
require -> precondition
inline function calls
overview of from general to specific in updates
initialize balance?