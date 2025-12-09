// SPDX-License-Identifier: MIT

pragma solidity ^0.8.0;

interface A1 {
  function setx(uint128 n) external;
}

contract A2 {
  A1 a;

  constructor(address c) {
    a = A1(c);
  }

  function setA1x(uint128 n) public {
    a.setx(n);
  }
}
