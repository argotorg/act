// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

contract A {
    constructor() payable {
    }

    function deposit() external payable {
    }

}

contract B {
    A av; // Act: A av := a

    constructor(address a) {
        av = A(a);
    }

    function deposit() external payable {
    }

    function transfer_to_A(uint256 amt) external {
        require(amt > 0, "amt=0");
        require(amt <= address(this).balance, "amt > BALANCE");

        av.deposit{value: amt}();
    }
}

